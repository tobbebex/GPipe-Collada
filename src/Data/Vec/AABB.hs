-----------------------------------------------------------------------------
--
-- Module      :  Data.Vec.AABB
-- Copyright   :  Tobias Bexelius
-- License     :  BSD3
--
-- Maintainer  :  Tobias Bexelius
-- Stability   :  Experimental
-- Portability :  Portable
--
-- |
-- This module provides an axis aligned bounding box based on 'Data.Vec's.
-----------------------------------------------------------------------------
module Data.Vec.AABB 
(
    AABB(..),
    aabbTransform,
    testAABBprojection,
    Intersection(..)
)

where
import Data.Monoid
import qualified Data.Vec.Base as Vec
import Data.Vec.Base ((:.)(..), Mat44, Mat33, Vec3)
import Data.Vec.Nat
import Data.Vec.LinAlg

-- | An axis aligned bounding box.
data AABB = AABB {
                aabbMin :: Vec3 Float,
                aabbMax :: Vec3 Float
            }
            deriving (Show, Eq)

instance Monoid AABB where
    mempty = let inf = read "Infinity" :: Float in AABB (Vec.vec inf) (Vec.vec (-inf))
    mappend (AABB minA maxA) (AABB minB maxB) = AABB (Vec.zipWith min minA minB) (Vec.zipWith max maxA maxB)

data Intersection = Inside | Intersecting | Outside deriving (Eq, Show, Ord, Enum, Bounded)

-- | Try if an 'AABB' is inside a projection frustum. The AABB must be defined in the same vector space as the matrix, e.g. use the model-view-projection matrix for model-local aabb's.
testAABBprojection :: Mat44 Float -> AABB -> Intersection
testAABBprojection m = 
    let planes = [-(row n3 m + row n0 m),
                  -(row n3 m - row n0 m),
                  -(row n3 m + row n1 m),
                  -(row n3 m - row n1 m),
                  -(row n3 m + row n2 m),
                  -(row n3 m - row n2 m)]
        getMin min max = min
        getMax min max = max
        vMinF = Vec.map (\ni -> if ni >= 0 then getMin else getMax)
        vMaxF = Vec.map (\ni -> if ni >= 0 then getMax else getMin)
        checkPlane (AABB bmin bmax) Outside _ = Outside
        checkPlane (AABB bmin bmax) state plane =
            let n = Vec.take n3 plane
                d = Vec.last plane
                vMin = Vec.zipWith ($) (Vec.zipWith ($) (vMinF n) bmin) bmax
                vMax = Vec.zipWith ($) (Vec.zipWith ($) (vMaxF n) bmin) bmax
            in if (n `dot` vMin) + d > 0 
                    then Outside
                    else if (n `dot` vMax) + d >= 0
                            then Intersecting
                            else Inside
    in \aabb -> foldl (checkPlane aabb) Inside planes

-- | Transforms an 'AABB* using a 4x4 matrix. Note that this may grow the AABB and is not associative with matrix multiplication, i.e.
-- 
-- > (m2 `multmm` m1) `aabbTransform` aabb
--
-- is usually not the same as
--
-- > m2 `aabbTransform` (m1 `aabbTransform` aabb)
--
-- (The former is preferred as it minimizes the growing of the AABB).
aabbTransform :: Mat44 Float -> AABB -> AABB
aabbTransform m (AABB bmin bmax) =
    let center = (bmax + bmin) / 2
        extent = bmax - center
        mAbs33 = Vec.map (Vec.map abs . Vec.take n3) $ Vec.take n3 m
        tcenter = project $ m `multmv` homPoint center
        textent = mAbs33 `multmv` extent
    in AABB (tcenter - textent) (tcenter + textent)
         
