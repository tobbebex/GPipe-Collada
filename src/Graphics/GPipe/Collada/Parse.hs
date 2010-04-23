-----------------------------------------------------------------------------
--
-- Module      :  Graphics.GPipe.Collada.Parse
-- Copyright   :  Tobias Bexelius
-- License     :  BSD3
--
-- Maintainer  :  Tobias Bexelius
-- Stability   :  Experimental
-- Portability :  Portable
--
-- |
-- This module provides the means to load Collada scene graphs from Collada (dae) files.
--
-- The parser supports Collada 1.5 core elements, including cameras lights and triangle meshes. Other elements such as animations, controllers or materials are ignored. Other meshes than
-- triangles, trifans and tristrips are ignored. Only float_arrays are supported and others will be ignored. The parser only support local links and will ignore external ones.
-- The parser supports parsing infinitely recursive structures into constant memory.
-----------------------------------------------------------------------------
module Graphics.GPipe.Collada.Parse
(
    readCollada,
    readColladaFile
)
where

import Graphics.GPipe.Collada
import Graphics.GPipe.Stream.Primitive
import Graphics.GPipe.Format

import Text.XML.HaXml hiding (Document, when, Reference, (!))
import qualified Text.XML.HaXml as XML
import Text.XML.HaXml.Parse
import Text.XML.HaXml.Posn

import Data.Tree (Tree(), Forest)
import qualified Data.Tree as Tree
import Data.Maybe
import Data.Monoid
import Data.Array
import Data.Function
import Data.List hiding (union)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Arrow (first, second)

import Data.Vec.Base ((:.)(..))
import qualified Data.Vec.Base as Vec
import Data.Vec.Nat
import Control.Monad.Error
import Control.Monad.Writer.Strict

import Data.Typeable
import Data.Dynamic

-- | Parse a string containing a collada document and return 'Either' an error message or the parsed Collada 'Scene'.
readCollada :: String -> Either String Scene
readCollada = readCollada' "Collada file"

-- | Open a Collada file and parse its contents and return a Collada 'Scene'. Errors are thrown as 'userError's.
readColladaFile :: FilePath -> IO Scene
readColladaFile f = do s <- readFile f
                       case readCollada' f s of
                        Left e -> throwError $ strMsg e
                        Right v -> return v

----------------------------------------------------------------
-- Parser type:

newtype RefMap = RefMap (Map ID (RefMap -> Reference))

data Reference = RefNode Scene
               | RefArray (Maybe ([Float], Int))
               | RefSource (Maybe ([[Float]], Int))
               | RefVertices (Map String ([[Float]], Int))
               | RefVisualScene Scene
               | RefCamera Camera
               | RefLight Light
               | RefGeometry Geometry

type Parser = WriterT [(ID, RefMap -> Reference)] (WriterT [RefMap -> Either String ()] (Either String))

runParser :: Parser (Maybe ID) -> Either String Reference
runParser m = do ((mid, refs), checks) <- runWriterT $ runWriterT m
                 case mid of
                    Nothing -> return $ RefVisualScene $ Tree.Node (nosid $ Node Nothing [] [] [] [] []) []
                    Just id -> do
                         let refmap = RefMap $ Map.fromList refs
                         mapM_ ($ refmap) checks
                         return $ fromJust $ getRef id refmap
                 
              
addRefF id ref = tell [(id, ref)]
getRef id a@(RefMap m) = fmap ($a) $ Map.lookup id m

assert f = lift $ tell [f]

----------------------------------------------------------------
-- Utility:

sid s a = (Just s, a)
nosid a = (Nothing, a)

localUrl ('#':id) = Just id
localUrl _ = Nothing

missingLinkErr el id c = el ++ " element with id '" ++ id ++ "' not found when processing " ++ errorPos c

errorPos c@(CElem (Elem n _ _) p) = n ++ " element in " ++ show p ++ "."

withError err m = m `mplus` throwError err

makeSID "" = nosid
makeSID s = sid s

changeTreeSID "" (Tree.Node (_, node) xs) = Tree.Node (nosid node) xs
changeTreeSID s (Tree.Node (_, node) xs) = Tree.Node (sid s node) xs

getAttribute s = fst . head . attributed s keep
getReqAttribute :: String -> Content Posn -> Parser String
getReqAttribute s c = case getAttribute s c of
                        "" -> throwError $ "Missing attribute " ++ s ++ " in " ++ errorPos c
                        a -> return a

getStringContent = intercalate " " . mapMaybe fst . textlabelled children

getReqSingleElement el c = case c -=> keep /> tag el of
                            [] -> throwError $ "Missing " ++ el ++ " element in " ++ errorPos c
                            [e] -> return e
                            _ -> throwError $ "Multiple " ++ el ++ " elements in " ++ errorPos c

getFromReqAttribute attr c = do a <- getReqAttribute attr c
                                fromString ("Malformed " ++ attr ++ " attribute in " ++ errorPos c) a

getFromAttributeDef attr def c = do let a = getAttribute attr c
                                    if null a
                                        then return def
                                        else fromString ("Malformed " ++ attr ++ " attribute in " ++ errorPos c) a

getFromSingleElementDef el def c = case c -=> keep /> tag el of
                                    [] -> return def
                                    [e] -> getFromContents e
                                    _ -> throwError $ "Multiple " ++ el ++ " elements in " ++ errorPos c

getFromListContents c = fromList ("Malformed contents of " ++ errorPos c) $ getStringContent c
getFromContents c = fromString ("Malformed contents of " ++ errorPos c) $ getStringContent c

getFromListLengthContents n c = do xs <- getFromListContents c
                                   if (length xs == n)
                                      then return xs
                                      else if (length xs < n)
                                            then throwError $ "Too few elements in " ++ errorPos c
                                            else throwError $ "Too many elements in " ++ errorPos c

fromList err = mapM (fromString err) . words
fromString err = parse . reads
    where parse [(a,"")] = return a
          parse _ = throwError err

infixl 2 ==>, -=>
xs ==> f = concatMap f xs
x -=> f = f x

----------------------------------------------------------------
----------------------------------------------------------------
----------------------------------------------------------------
-- Parser actions:

readCollada' f s = do p <- xmlParse' f s
                      xs <- withError "Expecting COLLADA top-element" $ do XML.Document _ _ (Elem "COLLADA" _ xs) _ <- return p
                                                                           return xs
                      RefVisualScene vs <- runParser $ parseDoc xs
                      return vs



parseDoc xs = do let sources = xs ==> deep (tagWith (flip elem ["animation","mesh","morph","skin","spline","convex_mesh","brep","nurbs","nurbs_surface"])) /> tag "source"
                 mapM_ parseArray $ sources ==> tagged (keep /> tagWith ("_array" `isSuffixOf`) `with` attr "id")
                 mapM_ parseSource $ sources
                 mapM_ parseCamera $ xs ==> tag "library_cameras" /> tag "camera" `with` attr "id"
                 mapM_ parseGeometry $ xs ==> tag "library_geometries" /> tag "geometry"
                 mapM_ parseLight $ xs ==> tag "library_lights" /> tag "light" `with` attr "id"
                 mapM_ parseNode $ xs ==> tag "library_nodes" /> tag "node"
                 mapM_ parseVisualScene $ xs ==> tag "library_visual_scenes" /> tag "visual_scene"
                 (url,c) <- case xs ==> attributed "url" (tag "scene" /> tag "instance_visual_scene") of
                       [] -> throwError $ "Missing scene element with instance_visual_scene element found in COLLADA top element."
                       [x] -> return x
                       _ -> throwError $ "Multiple instance_visual_scene elements in scene element found in COLLADA top element."
                 case localUrl url of
                        Nothing -> return Nothing
                        Just lurl -> do assert $ \refmap -> withError (missingLinkErr "visual_scene" lurl c) $ do Just (RefVisualScene _) <- return $ getRef lurl refmap
                                                                                                                  return ()
                                        return $ Just lurl

---------------------------------------------------------------


parseArray (s, arr) = do arrRef <- case s of 
                                    "float_array" -> do
                                        count <- getFromReqAttribute "count" arr
                                        xs <- getFromListContents arr
                                        let len = length xs
                                        when (len /= count)
                                            $ throwError $ "Length of array not the same as the value of count attribute in " ++ errorPos arr
                                        return $ Just (xs :: [Float], len)
                                    _ -> return Nothing
                         addRefF (getAttribute "id" arr) (const (RefArray arrRef))

---------------------------------------------------------------
          
parseSource s = do id <- getReqAttribute "id" s
                   sRef <- case s -=> keep /> tag "technique_common" of
                                [] -> return (const (RefSource Nothing))
                                tc:_ -> do acc <- getReqSingleElement "accessor" tc
                                           parseAccessor acc
                   addRefF id sRef

parseAccessor acc = do arrUrl <- getReqAttribute "source" acc
                       case localUrl arrUrl of
                            Nothing -> return (const (RefSource Nothing))
                            Just id -> do
                               count <- getFromReqAttribute "count" acc
                               offset <- getFromAttributeDef "offset" 0 acc
                               stride <- getFromAttributeDef "stride" 1 acc
                               useParamList <- mapM parseParam $ acc -=> keep /> elm
                               let paramLength = length useParamList
                               when (paramLength > stride)
                                   $ throwError $ "stride attribute too low in " ++ errorPos acc                              
                               let requiredLength = offset + stride * (count-1) + paramLength
                               assert $ \refmap -> do m <- withError (missingLinkErr "*_array" id acc) $ do Just (RefArray m) <- return $ getRef id refmap
                                                                                                            return m
                                                      case m of Just (_,len) | requiredLength > len -> throwError $ "Source size too small for " ++ errorPos acc 
                                                                _ -> return ()
                               return $ \refmap -> RefSource $ case getRef id refmap of
                                                                    Just (RefArray (Just (source, len))) -> Just (assembleSource (drop offset source) count stride useParamList, count)
                                                                    _ -> Nothing
    where parseParam c | null $ tag "param" c = throwError $ "Unexpected " ++ errorPos c
                       | otherwise = return $ not $ null $ getAttribute "name" c
          assembleSource source 0 _ _ = []
          assembleSource source count stride useParamList = case splitAt stride source of (vertex, rest) -> map snd (filter fst (zip useParamList vertex)) : assembleSource rest (count - 1) stride useParamList


---------------------------------------------------------------

parseNode c | not $ null $ tag "node" c = do
                    let id = getAttribute "id" c
                        mid = if id == "" then Nothing else Just id
                        sid = makeSID $ getAttribute "sid" c
                        layer = words $ getAttribute "layer" c
                    transformations <- fmap catMaybes $ mapM parseTransformations $ children c
                    cameraFs <- fmap catMaybes $ mapM parseCameraInstances $ c -=> keep /> tag "instance_camera"
                    lightFs <- fmap catMaybes $ mapM parseLightInstances $ c -=> keep /> tag "instance_light"                
                    geometryFs <- fmap catMaybes $ mapM parseGeometryInstances $ c -=> keep /> tag "instance_geometry"
                    subNodeFs <- fmap catMaybes $ mapM parseNode $ c -=> keep /> (tag "node" `union` tag "instance_node")
                    let treeF refmap = Tree.Node (sid (Node mid layer transformations (map ($refmap) cameraFs) (map ($refmap) lightFs) (map ($refmap) geometryFs))) (map ($refmap) subNodeFs)
                    case id of (_:_) -> addRefF id $ RefNode . treeF
                    return $ Just treeF
            | otherwise {- "instance_node" -} = do
                    url <- getReqAttribute "url" c
                    let sid = changeTreeSID $ getAttribute "sid" c
                    case localUrl url of
                            Just id -> do assert $ \refmap -> withError (missingLinkErr "instance_node" id c) $ do Just (RefNode _) <- return $ getRef id refmap
                                                                                                                   return ()
                                          return $ Just $ \refmap -> case getRef id refmap of Just (RefNode tree) -> sid $ tree
                            _ -> return Nothing

parseCameraInstances c = do url <- getReqAttribute "url" c
                            let sid = makeSID $ getAttribute "sid" c
                            case localUrl url of
                                Nothing -> return $ Nothing
                                Just id -> do assert $ \ refmap -> withError (missingLinkErr "instance_camera" id c) $ do Just (RefCamera _) <- return $ getRef id refmap
                                                                                                                          return ()
                                              return $ Just $ \ refmap -> case getRef id refmap of Just (RefCamera content) -> sid content
parseLightInstances c = do url <- getReqAttribute "url" c
                           let sid = makeSID $ getAttribute "sid" c
                           case localUrl url of
                                Nothing -> return $ Nothing
                                Just id -> do assert $ \ refmap -> withError (missingLinkErr "instance_light" id c) $ do Just (RefLight _) <- return $ getRef id refmap
                                                                                                                         return ()
                                              return $ Just $ \ refmap -> case getRef id refmap of Just (RefLight content) -> sid content
parseGeometryInstances c = do url <- getReqAttribute "url" c
                              let sid = makeSID $ getAttribute "sid" c
                              case localUrl url of
                                Nothing -> return $ Nothing
                                Just id -> do assert $ \ refmap -> withError (missingLinkErr "instance_camera" id c) $ do Just (RefGeometry _) <- return $ getRef id refmap
                                                                                                                          return ()
                                              return $ Just $ \ refmap -> case getRef id refmap of Just (RefGeometry content) -> sid content
---------------------------------------------------------------
parseTransformations c = do let sid = makeSID $ getAttribute "sid" c
                            case fst $ head $ tagged keep c of
                                "lookat" -> do xs <- getFromListLengthContents 9 c
                                               let (eye,rest) = splitAt 3 xs
                                                   (int, up) = splitAt 3 rest
                                               return $ Just $ sid $ LookAt (Vec.fromList eye) (Vec.fromList int) (Vec.fromList up)
                                "matrix" -> do mat <- getFromListLengthContents 16 c
                                               return $ Just $ sid $ Matrix $ Vec.matFromList mat
                                "rotate" -> do xs <- getFromListLengthContents 4 c
                                               let (rot,[a]) = splitAt 3 xs
                                               return $ Just $ sid $ Rotate (Vec.fromList rot) a
                                "scale" ->  do v <- getFromListLengthContents 3 c
                                               return $ Just $ sid $ Scale $ Vec.fromList v
                                "skew" ->   do xs <- getFromListLengthContents 7 c
                                               let ([a],rest) = splitAt 1 xs
                                                   (rot, trans) = splitAt 3 rest
                                               return $ Just $ sid $ Skew a (Vec.fromList rot) (Vec.fromList trans)
                                "translate" -> do v <- getFromListLengthContents 3 c
                                                  return $ Just $ sid $ Translate $ Vec.fromList v
                                _ -> return $ Nothing
---------------------------------------------------------------

parseVisualScene c = do let id = getAttribute "id" c
                        subNodeFs <- fmap catMaybes $ mapM parseNode $ c -=> keep /> tag "node"
                        unless (null id) $
                            addRefF id $ \refmap -> RefVisualScene $ Tree.Node (nosid $ Node (Just id) [] [] [] [] []) $ map ($ refmap) subNodeFs
                                                
---------------------------------------------------------------

parseCamera c = do let id = getAttribute "id" c
                   optics <- getReqSingleElement "optics" c
                   tech <- getReqSingleElement "technique_common" optics
                   camera <- case (tech -=> keep /> tag "perspective", tech -=> keep /> tag "ortographic") of
                                ([persp], []) -> do fov <- parseViewSize (persp -=> keep /> tag "xfov") (persp -=> keep /> tag "yfov") (persp -=> keep /> tag "aspect_ratio")
                                                                         ("Missing valid combination of xfov, yfov and aspect_ratio elements in " ++ errorPos persp)
                                                    z <- parseZ persp
                                                    return $ Perspective id fov z
                                ([], [orth]) -> do mag <- parseViewSize (orth -=> keep /> tag "xmag") (orth -=> keep /> tag "ymag") (orth -=> keep /> tag "aspect_ratio")
                                                                        ("Missing valid combination of xmag, ymag and aspect_ratio elements in " ++ errorPos orth)
                                                   z <- parseZ orth
                                                   return $ Orthographic id mag z
                                _ -> throwError $ "Excpected one perspective or ortographic element at " ++ errorPos tech
                   addRefF id $ const $ RefCamera camera
    where 
        parseViewSize [x] [] [] _  = do x' <- getFromContents x
                                        return $ ViewSizeX x'
        parseViewSize [] [y] [] _  = do y' <- getFromContents y
                                        return $ ViewSizeY y'
        parseViewSize [x] [y] [] _ = do x' <- getFromContents x
                                        y' <- getFromContents y
                                        return $ ViewSizeXY (x':.y':.())
        parseViewSize [x] [] [a] _ = do x' <- getFromContents x
                                        a' <- getFromContents a
                                        let y' = x' / a'
                                        return $ ViewSizeXY (x':.y':.())
        parseViewSize [] [y] [a] _ = do y' <- getFromContents y
                                        a' <- getFromContents a
                                        let x' = y' * a'
                                        return $ ViewSizeXY (x':.y':.())
        parseViewSize _ _ _ err     = throwError err
        parseZ c = do near <- getReqSingleElement "znear" c
                      znear <- getFromContents near
                      far <- getReqSingleElement "zfar" c
                      zfar <- getFromContents far
                      return $ Z znear zfar
                                              
parseGeometry c = do verticess <- mapM (getReqSingleElement "vertices") $ c -=> keep /> cat [tag "convex_mesh", tag "brep"]
                     mapM_ parseVertices verticess
                     mesh <- getReqSingleElement "mesh" c
                     parseMesh (getAttribute "id" c) mesh
                     
parseLight c = do let id = getAttribute "id" c
                  tech <- getReqSingleElement "technique_common" c
                  light <- case (tech -=> keep /> tag "ambient", tech -=> keep /> tag "directional", tech -=> keep /> tag "point", tech -=> keep /> tag "spot") of
                                ([a],[],[],[]) -> do color <- parseSubColor a
                                                     return $ Ambient id color
                                ([],[a],[],[]) -> do color <- parseSubColor a
                                                     return $ Directional id color
                                ([],[],[a],[]) -> do color <- parseSubColor a
                                                     att <- parseSubAttenuation a
                                                     return $ Point id color att
                                ([],[],[],[a]) -> do color <- parseSubColor a
                                                     att <- parseSubAttenuation a
                                                     ang <- getFromSingleElementDef "falloff_angle" 180 c
                                                     exp <- getFromSingleElementDef "falloff_exponent" 0 c
                                                     return $ Spot id color att ang exp
                                _ -> throwError $ "Excpected one ambient, directional, point or spot element at " ++ errorPos tech
                  addRefF id $ const $ RefLight light
    where
        parseSubColor c = do color <- getReqSingleElement "color" c
                             colors <- getFromListLengthContents 3 color
                             return $ RGB $ Vec.fromList colors
        parseSubAttenuation c = do con <- getFromSingleElementDef "constant_attenuation" 1 c
                                   lin <- getFromSingleElementDef "linear_attenuation" 0 c
                                   qua <- getFromSingleElementDef "quadratic_attenuation" 0 c
                                   return $ Attenuation con lin qua

---------------------------------------------------------------
-- Mesh parsing:

parseMesh id c = do v <- getReqSingleElement "vertices" c
                    vertices <- parseVertices v
                    if null id 
                     then return ()
                     else do
                        dynPrimListFs <- fmap concat $ mapM (parsePrimitives vertices) $ children c
                        addRefF id $ \refmap -> let dynPrimLists = map (second ($refmap)) dynPrimListFs
                                                in RefGeometry $ Mesh id (makeDynPrimStream dynPrimLists)

          
parseVertices verts = do insF <- fmap (map snd) $ mapM (parseInput False) $ verts -=> keep /> tag "input"
                         let vertsF = \refmap -> Map.unions $ map ($refmap) insF
                         case getAttribute "id" verts of
                            "" -> return ()
                            id -> addRefF id $ RefVertices . vertsF 
                         return vertsF

parseInput :: Bool -> Content Posn -> Parser (Int, RefMap -> Map String ([[Float]], Int))
parseInput shared i = do source <- getReqAttribute "source" i
                         offset <- if shared
                                   then getFromReqAttribute "offset" i
                                   else return undefined
                         case localUrl source of
                            Nothing -> return (offset, const Map.empty)
                            Just id -> do
                                semantic <- getReqAttribute "semantic" i
                                let set = if shared then getAttribute "set" i else ""
                                assert $ \refmap -> case (shared, semantic, getRef id refmap) of
                                                         (true, "VERTEX", Just (RefVertices _)) -> return ()
                                                         (true, "VERTEX", _) -> throwError $ missingLinkErr "vertices" id i
                                                         (_, _, Just (RefSource _)) -> return ()
                                                         _ -> throwError $ missingLinkErr "source" id i
                                let f = \ refmap -> case (shared, semantic, getRef id refmap) of
                                                         (true, "VERTEX", Just (RefVertices m)) -> Map.mapKeysMonotonic (++set) m
                                                         (_, _, Just (RefSource Nothing)) -> Map.empty
                                                         (_, _, Just (RefSource (Just source))) -> Map.singleton (semantic++set) source
                                return (offset, f)
                                                                       
              
parsePrimitives vertices p = case mprimtype of
                       Nothing -> return mempty
                       Just primtype -> do
                               inputFs' <- fmap (Map.fromListWith combine) $ mapM (parseInput True) $ p -=> keep /> tag "input"
                               let inputFs = if Map.null inputFs'
                                                then Map.singleton 0 vertices
                                                else inputFs'
                               count <- getFromReqAttribute "count" p
                               if count == 0
                                    then return []
                                    else do ps' <- case (primtype, ps) of
                                                (TriangleList, _:_:_) -> throwError $ "Multiple p elements in " ++ errorPos p
                                                (TriangleList, [_]) -> return ps
                                                (TriangleList, []) -> throwError $ "Missing p element in " ++ errorPos p
                                                (_, _:_) | length ps < count -> throwError $ "Too few p elements in " ++ errorPos p
                                                _ -> return $ take count ps
                                            mapM (parseP primtype inputFs count) ps'
    where mprimtype = case fst $ head $ tagged keep p of
            "triangles" -> Just TriangleList
            "trifans" -> Just TriangleFan
            "tristrips" -> Just TriangleStrip
            _ -> Nothing
          ps = p -=> keep /> tag "p"
          combine :: (RefMap -> Map String ([[Float]], Int)) -> (RefMap -> Map String ([[Float]], Int)) -> (RefMap -> Map String ([[Float]], Int))
          combine f g = \refmap -> f refmap `Map.union` g refmap

parseP :: Triangle -> Map Int (RefMap -> Map String ([[Float]], Int)) -> Int -> Content Posn -> Parser ((String, Triangle, Maybe [Int]), RefMap -> Map String [[Float]])
parseP primtype inputs count p = do let pStride = 1 + fst (Map.findMax inputs)
                                        material = getAttribute "material" p
                                    pLists <- fmap (splitIn pStride) $ do
                                                    pl <- getFromListContents p
                                                    if (primtype == TriangleList)
                                                        then do when (length pl < count * 3 * pStride) $ throwError $ "Too few indices in " ++ errorPos p
                                                                return $ take (count * 3 * pStride) pl
                                                        else return pl
                                    case map (first (pLists !!)) $ Map.toList inputs of
                                            [(indices,mF)] -> return ((material, primtype, Just indices), Map.map fst . mF)
                                            xs -> return ((material, primtype, Nothing), combine $ map pickIndices xs)
    where pickIndices (indices, mF) = \refmap -> Map.map pickIndices' (mF refmap)
                where pickIndices' (xs, len) = let arr = listArray (0,len) xs in map (arr!) indices
          combine mFs = \refmap -> Map.unions $ map ($refmap) mFs
          splitIn n = reverse . transpose . splitIn' [] n -- [[offset 0], [offset 1], [offset 2]]
                where
                    splitIn' acc 0 xs = acc:splitIn' [] n xs
                    splitIn' acc _ [] = []
                    splitIn' acc m (x:xs) = splitIn' (x:acc) (m-1) xs
        

-----------------------------------------------------
-- Dynamic Vertex

makeDynPrimStream = map makePrimGroup . groupBy ((==) `on` fst) . map splitParts
splitParts ((material, primtype, mindices), m) = let mlist = Map.toAscList m
                                                     ins = transpose $ map snd mlist
                                                     names = map fst mlist
                                                     sizes = map length $ head ins
                                                     input = map concat ins
                                                     aabb = makeAABB $ Map.lookup "POSITION" m
                                                 in ((material, names, sizes), (aabb,((primtype, mindices), input))) 


makeAABB Nothing = AABB (Vec.vec (-inf)) (Vec.vec (inf))
makeAABB (Just xs) = mconcat $ map pointToAABB xs
                where pointToAABB (x:y:z:_) = let p = x:.y:.z:.() in AABB p p
                      pointToAABB (x:y:_) = AABB (x:.y:.(-inf):.()) (x:.y:.(inf):.())
                      pointToAABB (x:_) = AABB (x:.(-inf):.(-inf):.()) (x:.(inf):.(inf):.())
                      pointToAABB (_) = AABB (Vec.vec (-inf)) (Vec.vec inf)

inf :: Float
inf = read "Infinity"                      
                
makeTypeRep n = dynTypeRep $ makeDyn n undefined
takeBy (size:sizes) xs = case splitAt size xs of (a,b) -> a : takeBy sizes b
takeBy [] _ = []

makePrimGroup xs@(((material, names, sizes), _):_) = TriangleMesh material desc pstream aabb
    where 
          xs' = map (second snd) xs
          aabb = mconcat $ map (fst . snd) xs
          desc = Map.fromAscList $ zip names $ map makeTypeRep sizes
          pstream = fmap (Map.fromAscList . zip names . map (uncurry makeDyn) . zip sizes . takeBy sizes) $ makeListStream (sum sizes) xs'           

type S2 a = Succ (Succ a)
type S4 a = S2 (S2 a)
type S10 a = S2 (S4 (S4 a))

s10 :: forall a. Nat a => a -> S10 a
s10 _ = undefined :: S10 a

toStreamUsingLength n = fmap (Vec.toList . withLength n) . mconcat . map (toPrimStream . second (second (map Vec.fromList)))
withLength n v = v `asTypeOf` Vec.mkVec n (undefined :: Vertex Float)
toPrimStream (_, ((primtype, Just indices), input)) = toIndexedGPUStream primtype input indices
toPrimStream (_, ((primtype, _), input)) = toGPUStream primtype input

makeDyn n = case n of 
    0 -> const $ toDyn ()
    1 -> toDyn . head
    2 -> toDyn . withLength n2 . Vec.fromList
    3 -> toDyn . withLength n3 . Vec.fromList
    4 -> toDyn . withLength n4 . Vec.fromList
    5 -> toDyn . withLength n5 . Vec.fromList
    6 -> toDyn . withLength n6 . Vec.fromList
    7 -> toDyn . withLength n7 . Vec.fromList
    8 -> toDyn . withLength n8 . Vec.fromList
    9 -> toDyn . withLength n9 . Vec.fromList
    10 -> toDyn . withLength n10 . Vec.fromList
    11 -> toDyn . withLength n11 . Vec.fromList
    12 -> toDyn . withLength n12 . Vec.fromList
    13 -> toDyn . withLength n13 . Vec.fromList
    14 -> toDyn . withLength n14 . Vec.fromList
    15 -> toDyn . withLength n15 . Vec.fromList
    16 -> toDyn . withLength n16 . Vec.fromList

makeListStream n = case n of
    0 -> fmap (\() -> []) . mconcat . map (toPrimStream . second (second (map (const ()))))
    1 -> fmap (:[]) . mconcat . map (toPrimStream . second (second (map head)))
    2 -> toStreamUsingLength n2
    3 -> toStreamUsingLength n3
    4 -> toStreamUsingLength n4
    5 -> toStreamUsingLength n5
    6 -> toStreamUsingLength n6
    7 -> toStreamUsingLength n7
    8 -> toStreamUsingLength n8
    9 -> toStreamUsingLength n9
    10 -> toStreamUsingLength n10
    11 -> toStreamUsingLength n11
    12 -> toStreamUsingLength n12
    13 -> toStreamUsingLength n13
    14 -> toStreamUsingLength n14
    15 -> toStreamUsingLength n15
    16 -> toStreamUsingLength n16
    17 -> toStreamUsingLength n17
    18 -> toStreamUsingLength n18
    19 -> toStreamUsingLength n19
    20 -> toStreamUsingLength $ s10 n10
    21 -> toStreamUsingLength $ s10 n11
    22 -> toStreamUsingLength $ s10 n12
    23 -> toStreamUsingLength $ s10 n13
    24 -> toStreamUsingLength $ s10 n14
    25 -> toStreamUsingLength $ s10 n15
    26 -> toStreamUsingLength $ s10 n16
    27 -> toStreamUsingLength $ s10 n17
    28 -> toStreamUsingLength $ s10 n18
    29 -> toStreamUsingLength $ s10 n19
    30 -> toStreamUsingLength $ s10 $ s10 n10
    31 -> toStreamUsingLength $ s10 $ s10 n11
    32 -> toStreamUsingLength $ s10 $ s10 n12
    33 -> toStreamUsingLength $ s10 $ s10 n13
    34 -> toStreamUsingLength $ s10 $ s10 n14
    35 -> toStreamUsingLength $ s10 $ s10 n15
    36 -> toStreamUsingLength $ s10 $ s10 n16
    37 -> toStreamUsingLength $ s10 $ s10 n17
    38 -> toStreamUsingLength $ s10 $ s10 n18
    39 -> toStreamUsingLength $ s10 $ s10 n19
    40 -> toStreamUsingLength $ s10 $ s10 $ s10 n10
    41 -> toStreamUsingLength $ s10 $ s10 $ s10 n11
    42 -> toStreamUsingLength $ s10 $ s10 $ s10 n12
    43 -> toStreamUsingLength $ s10 $ s10 $ s10 n13
    44 -> toStreamUsingLength $ s10 $ s10 $ s10 n14
    45 -> toStreamUsingLength $ s10 $ s10 $ s10 n15
    46 -> toStreamUsingLength $ s10 $ s10 $ s10 n16
    47 -> toStreamUsingLength $ s10 $ s10 $ s10 n17
    48 -> toStreamUsingLength $ s10 $ s10 $ s10 n18
    49 -> toStreamUsingLength $ s10 $ s10 $ s10 n19
    50 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 n10
    51 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 n11
    52 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 n12
    53 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 n13
    54 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 n14
    55 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 n15
    56 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 n16
    57 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 n17
    58 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 n18
    59 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 n19
    60 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 $ s10 n10
    61 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 $ s10 n11
    62 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 $ s10 n12
    63 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 $ s10 n13
    64 -> toStreamUsingLength $ s10 $ s10 $ s10 $ s10 $ s10 n14          
    
