{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable #-}
-----------------------------------------------------------------------------
--
-- Module      :  Graphics.GPipe.Collada
-- Copyright   :  Tobias Bexelius
-- License     :  BSD3
--
-- Maintainer  :  Tobias Bexelius
-- Stability   :  Experimental
-- Portability :  Portable
--
-- |
-- This module contains the data types of the Collada scene graph.
--
-- Orphan TypeableX instances are also provided for 'Vertex' and "Data.Vec" vectors (:.) .
-----------------------------------------------------------------------------
module Graphics.GPipe.Collada 
(
    Scene,
    
    Node(..),
    nodeMat,
    nodeAABB,

    Transform(..),
    transformMat,
    transformsMat,

    Camera(..),
    cameraMat,
    
    ViewSize(..),
    Z(..),
    
    Light(..),
    Attenuation(..),
    
    Geometry(..),
    Mesh(..),
    ID,
    SID,
    Semantic,
    AABB(..)    
)
where

import Data.Tree
import Data.Map (Map)
import Data.Maybe
import Data.Monoid
import Graphics.GPipe.Stream
import Graphics.GPipe.Stream.Primitive
import Graphics.GPipe.Format
import qualified Data.Vec as Vec
import Data.Vec (Vec2, Vec3, Mat44, Mat33, (:.)(..), )
import Data.Vec.LinAlg
import Data.Vec.AABB

import Data.Typeable
import Data.Dynamic

type Scene = Tree (SID, Node)

data Node = Node {
                nodeId :: Maybe ID,
                nodeLayers :: [String],
                nodeTransformations :: [(SID, Transform)],
                nodeCameras :: [(SID, Camera)],
                nodeLights :: [(SID, Light)],
                nodeGeometries :: [(SID, Geometry)]
                }
                deriving (Show)

data Transform = LookAt {
                    lookAtEye:: Vec3 Float,
                    lookAtInterest :: Vec3 Float,
                    lookAtUp :: Vec3 Float
                 }
               | Matrix (Mat44 Float)
               | Rotate (Vec3 Float) Float
               | Scale (Vec3 Float) 
               | Skew {
                    skewAngle :: Float,
                    skewRotation :: Vec3 Float,
                    skewTranslation :: Vec3 Float
                 }
               | Translate (Vec3 Float) 
               deriving (Show, Eq)

data Camera = Perspective {
                perspectiveID :: ID,
                perspectiveFov :: ViewSize,
                perspectiveZ :: Z
              }
            | Orthographic {
                orthographicID :: ID,
                orthographicViewSize :: ViewSize,
                orthographicZ :: Z
              }
              deriving (Show, Eq)

data ViewSize = ViewSizeX Float
              | ViewSizeY Float
              | ViewSizeXY (Vec2 Float)
              deriving (Show, Eq)

data Z = Z { 
            zNear :: Float, 
            zFar :: Float
           }
           deriving (Show, Eq)
            
data Light = Ambient {
                ambientID :: ID,
                ambientColor :: Color RGBFormat Float
             }
           | Directional {
                directionalID :: ID,
                directionalColor :: Color RGBFormat Float
             }
           | Point {
                pointID :: ID,
                pointColor :: Color RGBFormat Float,
                pointAttenuation :: Attenuation
             }
           | Spot {
                spotID :: ID,
                spotColor :: Color RGBFormat Float,
                spotAttenuation :: Attenuation,
                spotFallOffAngle :: Float,
                spotFallOffExponent :: Float
             }
              deriving (Show, Eq)

data Attenuation = Attenuation {
                attenuationConstant :: Float,
                attenuationLinear :: Float,
                attenuationQuadratic :: Float
            }
              deriving (Show, Eq)

data Geometry = Mesh {
                meshID :: ID,
                meshPrimitives :: [Mesh]
            }
              deriving (Show)

data Mesh = TriangleMesh {
                meshMaterial :: String,
                meshDescription :: Map Semantic TypeRep,
                meshPrimitiveStream :: PrimitiveStream Triangle (Map Semantic Dynamic),
                meshAABB :: AABB
            }

instance Show Mesh where
    show (TriangleMesh a b _ d) = "TriangleMesh {meshMaterial = " ++ show a ++ ", meshDescription = " ++ show b ++ ", meshPrimitiveStream = PrimitiveStream Triangle (Map String Dynamic), meshAABB = " ++ show d ++"}"

type ID = String
type SID = Maybe String
type Semantic = String

deriving instance Typeable2 Shader
deriving instance Typeable V
deriving instance Typeable2 (:.)

---------------------------------------------------

toRadians :: Floating a => a -> a
toRadians d = d * pi / 180

-- | Gets the projection matrix of a 'Camera' element.
cameraMat :: Float -> Camera -> Mat44 Float
cameraMat asp (Perspective _ (ViewSizeX x) (Z near far)) = perspective near far (toRadians x / asp) asp
cameraMat asp (Perspective _ (ViewSizeY y) (Z near far)) = perspective near far (toRadians y) asp
cameraMat _ (Perspective _ (ViewSizeXY (x:.y:.())) (Z near far)) = perspective near far (toRadians y) (x/y)
cameraMat asp (Orthographic _ (ViewSizeX x) (Z near far)) = orthogonal near far (x :.  (x/asp) :. ())
cameraMat asp (Orthographic _ (ViewSizeY y) (Z near far)) = orthogonal near far ((y*asp) :.  y :. ())
cameraMat _ (Orthographic _ (ViewSizeXY s) (Z near far)) = orthogonal near far s

-- | Gets the transformation matrix of a 'Transform' element.
transformMat :: Transform -> Mat44 Float
transformMat (LookAt e i u) = rotationLookAt u e i
transformMat (Matrix m) = m
transformMat (Rotate v a) = rotationVec v (toRadians a)
transformMat (Scale v) = scaling v
transformMat (Skew a r t) = skew (toRadians a) r t
transformMat (Translate v) = translation v

-- | Gets the total transformation matrix of a list of 'Transform' element.
transformsMat :: [Transform] -> Mat44 Float
transformsMat = foldl multmm identity . map transformMat

----------------------------------
-- adopted from http://www.koders.com/cpp/fidA08C276050F880D11C2E49280DD9997478DC5BA1.aspx
skew :: Float -> Vec3 Float -> Vec3 Float -> Mat44 Float
skew angle a b = Vec.map homVec m `Vec.snoc` homPoint 0
    where
        n2 = normalize b
        a1 = Vec.map (* (a `dot` n2)) n2
        a2 = a-a1
        n1 = normalize a2
        an1 = a `dot` n1
        an2 = a `dot` n2
        rx = an1 * cos angle - an2 * sin angle
        ry = an1 * sin angle + an2 * cos angle
        alpha = if abs an1 < 0.000001 then 0 else ry/rx-an2/an1
        m = outerProd n1 (Vec.map (* alpha) n2) + identity
        
        outerProd :: Vec3 Float -> Vec3 Float -> Mat33 Float
        outerProd a b = Vec.map (* b) $ Vec.map Vec.vec a

-- | The complete transform matrix of all 'Transform' elements in a node.
nodeMat :: Node -> Mat44 Float
nodeMat = transformsMat . map snd . nodeTransformations

-- | The smallest 'AABB' that contains all 'Geometry' elements in a node. Note: This is not transformed using the nodes 'Transform' elements.
nodeAABB :: Node -> AABB
nodeAABB = mconcat . map (mconcat . map meshAABB . meshPrimitives . snd) . nodeGeometries
