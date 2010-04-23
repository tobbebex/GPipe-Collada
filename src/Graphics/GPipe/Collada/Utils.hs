-----------------------------------------------------------------------------
--
-- Module      :  Graphics.GPipe.Collada.Utils
-- Copyright   :  Tobias Bexelius
-- License     :  BSD3
--
-- Maintainer  :  Tobias Bexelius
-- Stability   :  Experimental
-- Portability :  Portable
--
-- |
-- This module contains the data types of the Collada scene graph.
-----------------------------------------------------------------------------
module Graphics.GPipe.Collada.Utils
(
    -- * General Tree utilities
    topDown,
    bottomUp,
    prune,
    
    -- * Scene utilities
    SIDPath,
    topDownSIDPath,
    topDownTransform,

    -- * SID utilities
    alterSID,
    lookupSID,
    
    -- * Geometry utilities
    hasDynVertex,
    dynVertex,
    
    -- * Debug utilities
    viewScene
)
where

import Debug.Trace
import Graphics.GPipe.Collada
import Graphics.GPipe
import Data.Tree (Tree(), Forest)
import qualified Data.Tree as Tree
import Data.Maybe
import qualified Data.Vec.Base as Vec
import Data.Vec.Base ((:.)(..), Mat44, Mat33, Vec3)
import Data.Vec.LinAlg as Vec
import Data.Vec.LinAlg.Transform3D
import Data.Vec.Nat
import Control.Arrow (first)
import Data.Monoid
import Data.Dynamic
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Foldable as F
import Control.Monad
import Data.Vec.AABB

-- | Traverse a Tree top down, much like 'mapAccumL'. The function recieves an accumulator from its parent and generates one that is passed down to its children.
--   Useful for accumulating transformations, etc.
topDown :: (acc -> x -> (acc, y)) -> acc -> Tree x -> Tree y
topDown f a (Tree.Node x xs) = case f a x of (acc', y) -> Tree.Node y $ map (topDown f acc') xs

-- | Traverse a Tree bottom up, much like 'mapAccumR'. The function recieves the accumulators of all its children and generates one that is passed up to its parent.
--   Useful for accumulating AABBs, etc.
bottomUp :: ([acc] -> x -> (acc, y)) -> Tree x -> (acc, Tree y)
bottomUp f (Tree.Node x xs) = case unzip $ map (bottomUp f) xs of (accs, ys) -> case f accs x of (acc', y) -> (acc', Tree.Node y ys)

-- | Remove branches of a tree where the function evaluates to 'True'. Useful for selecting LODs, etc.
prune :: (a -> Bool) -> Tree a -> Maybe (Tree a)
prune f (Tree.Node x xs) = if f x then Nothing else Just $ Tree.Node x $ mapMaybe (prune f) xs


---------------------------------
-- | A path where the first string in the list is the closest ID and the rest is all SIDs found in order.
type SIDPath = [String]

-- | Traverse a tree top down accumulating the 'SIDPath' for each node. The projection function enables this to be used on trees that are not 'Scene's.
--   The accumulated 'SIDPath' for a node will include the node's 'SID' at the end, but not its 'ID'. The 'ID' will however be the first 'String' in the
--   'SIDPath's of the children, and the nodes 'SID' won't be included in this case.
topDownSIDPath :: (x -> (SID, Maybe ID)) -> Tree x -> Tree (SIDPath,x)
topDownSIDPath f = topDown g [] 
    where g p x = case f x of
                    (msid, mid) -> let p' = p ++ maybeToList msid
                                   in (maybe p' (:[]) mid, (p', x))

-- | Traverse a tree top down accumulating the absolute transform for each node. The projection function enables this to be used on trees that are not 'Scene's.
--   Use 'nodeMat' to get the @Mat44 Float@ from a node. The accumulated matrix for each node will contain the node's own transforms.
topDownTransform :: (x -> Mat44 Float) -> Tree x -> Tree (Mat44 Float,x)
topDownTransform f = topDown g identity
    where g t x = let t' = t `multmm` (f x) in (t', (t', x))

-- | For each 'SID'-attributed element in a list, apply the provided function. The elements where the function evaluates to 'Nothing' are removed.
alterSID :: (String -> a -> Maybe a) -> [(SID,a)] -> [(SID,a)]
alterSID f = mapMaybe (alterSID' f)
    where
        alterSID' f (msid@(Just sid), x) = fmap ((,) msid) $ f sid x
        alterSID' _ a = Just a
        
-- | Find the first element in the list that is attributed with the provided SID.
lookupSID :: String -> [(SID,a)] -> Maybe a
lookupSID = lookup . Just

-- | Evaluates to 'True' where the 'Map' contains the semantic with the same type as the last argument (which is not evaluated and prefferably is a monotyped 'undefined').
hasDynVertex :: Typeable a => Map Semantic TypeRep -> Semantic -> a -> Bool
hasDynVertex m s a = maybe False (== typeOf a) $ Map.lookup s m

-- | Extract the value of a specific semantic from the 'Map'. If the semantic is not found or the type is wrong, it evaluates to 'Nothing'.
dynVertex :: Typeable a => Map Semantic Dynamic -> Semantic -> Maybe a
dynVertex m s = Map.lookup s m >>= fromDynamic

-----------------------------------------

-- | Render the scene using a simple shading technique through the first camera found, or through a defult camera if the scene doesn't contain any cameras. The scene's lights aren't
--   used in the rendering. The source of this function can also serve as an example of how a Collada 'Scene' can be processed.
viewScene :: Scene -> Vec2 Int -> FrameBuffer RGBFormat DepthFormat ()
viewScene tree (w:.h:.()) = framebuffer
    where
      aspect = fromIntegral w / fromIntegral h
      
      -- Retrieve cameras and geometries tagged with transforms
      (cameras,geometries) = F.foldMap tagContent $ topDownTransform nodeMat $ fmap snd tree
      tagContent (t,n) = let tagT = zip (repeat t) in (tagT $ nodeCameras n, tagT $ nodeGeometries n) 

      -- Get the camera and inverted view matrix
      (invView,cam) = head (cameras ++ [(translation (0:.0:.100:.()) , (Nothing, Perspective "" (ViewSizeY 35) (Z 1 10000)))])
      
      -- The transform matrices
      view = fromJust $ invert invView
      proj = cameraMat aspect $ snd cam
      viewProj = proj `multmm` view
            
      framebuffer = paint fragmentStream $ newFrameBufferColorDepth (RGB 0) 1
      paint = paintColorRastDepth Lequal True NoBlending (RGB $ Vec.vec True)      
      fragmentStream = fmap (RGB . Vec.vec) $ rasterizeFront primitiveStream
      primitiveStream = mconcat $ concatMap filterGeometry geometries
      filterGeometry (modelMat, (_,Mesh _ mesh)) = mapMaybe (filterMesh (viewProj `multmm` modelMat) (view `multmm` modelMat) modelMat) mesh
      filterMesh modelViewProj modelView modelMat (TriangleMesh _ desc pstream aabb) = do
        guard $ hasDynVertex desc "POSITION" (undefined :: Vec3 (Vertex Float)) -- Filter out geometries without 3D-positions
        guard $ hasDynVertex desc "NORMAL" (undefined :: Vec3 (Vertex Float))   -- Filter out geometries without 3D-normals
        guard $ testAABBprojection modelViewProj aabb /= Outside                -- Frustum cull geometries
        let normMat = Vec.transpose $ fromJust $ invert $ Vec.map (Vec.take n3) $ Vec.take n3 modelView
        return $ fmap (\v -> let p = homPoint $ fromJust $ dynVertex v "POSITION"
                                 nx:.ny:.nz:.() = (toGPU normMat :: Mat33 (Vertex Float)) `multmv` fromJust (dynVertex v "NORMAL")
                             in ((toGPU modelViewProj :: Mat44 (Vertex Float)) `multmv` p, max nz 0)
                      ) pstream
            
