{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use guards" #-}
{-# HLINT ignore "Use zipWith" #-}
{-# LANGUAGE FlexibleContexts #-}


module Quickhull (

  Point, Line, SegmentedPoints,
  quickhull,

  -- Exported for display
  initialPartition,
  partition,

  -- Exported just for testing
  propagateL, shiftHeadFlagsL, segmentedScanl1,
  propagateR, shiftHeadFlagsR, segmentedScanr1,

) where

import Data.Array.Accelerate
import Data.Array.Accelerate.Debug.Trace
import qualified Prelude                      as P
import Data.Array.Accelerate.Data.Maybe (isJust, maybe)
import Data.Array.Accelerate.Smart


-- Points and lines in two-dimensional space
--
type Point = (Int, Int)
type Line  = (Point, Point)

-- This algorithm will use a head-flags array to distinguish the different
-- sections of the hull (the two arrays are always the same length).
--
-- A flag value of 'True' indicates that the corresponding point is
-- definitely on the convex hull. The points after the 'True' flag until
-- the next 'True' flag correspond to the points in the same segment, and
-- where the algorithm has not yet decided whether or not those points are
-- on the convex hull.
--
type SegmentedPoints = (Vector Bool, Vector Point)


-- Core implementation
-- -------------------

-- Initialise the algorithm by first partitioning the array into two
-- segments. Locate the left-most (p₁) and right-most (p₂) points. The
-- segment descriptor then consists of the point p₁, followed by all the
-- points above the line (p₁,p₂), followed by the point p₂, and finally all
-- of the points below the line (p₁,p₂).
--
-- To make the rest of the algorithm a bit easier, the point p₁ is again
-- placed at the end of the array.
--
-- We indicate some intermediate values that you might find beneficial to
-- compute.
--

expTrue, expFalse :: Exp Bool
expTrue = the $ use (fromList Z [True])
expFalse = the $ use (fromList Z [False])

-- acc and value maybe have to be turned around
minimumBy :: Elt a => (Exp a -> Exp a -> Exp Bool) -> Acc (Vector a) -> Acc (Scalar a)
minimumBy comparator = fold1 (\acc value -> if comparator acc value then acc else value)

-- some trickery is used to eliminate division
pointIsOnLine :: Exp Line -> Exp Point -> Exp Bool
pointIsOnLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = dy * x + dx * y1 - dy * x1 == dx * y  where
  dx = x2 - x1
  dy = y2 - y1

-- Make sure each True value is mapped to the right True index
-- for example: [True, False, False, True, True, True, False, True] -> [0, _, _, 1, 2, 3, _, 4]
boolToOffset :: Acc (Vector Bool) -> Acc (Vector Int)
boolToOffset array = map (\i -> i - 1) $ scanl1 (+) arrayToInt where
    arrayToInt = map (\b -> if b then 1 else 0) array

initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
      p1, p2 :: Exp Point
      p1 = the $ minimumBy (<) points
      p2 = the $ minimumBy (>) points

      isUpper :: Acc (Vector Bool)
      isUpper = map (pointIsLeftOfLine (T2 p1 p2)) points

      isLower :: Acc (Vector Bool)
      isLower = map (\p -> (not . pointIsLeftOfLine (T2 p1 p2)) p && (not . pointIsOnLine (T2 p1 p2)) p) points

      offsetUpper :: Acc (Vector Int)
      countUpper  :: Acc (Scalar Int)
      T2 offsetUpper countUpper = T2 offset count where
        count = unit $ (offset !! (length offset - 1)) + 1
        offset = boolToOffset isUpper

      offsetLower :: Acc (Vector Int)
      offsetLower = boolToOffset isLower

      -- map each point to the index it will have in the new list, so that in can be thrown in a permute function
      destinations :: Acc (Vector (Maybe DIM1))
      destinations = map mapper (zip5 points isUpper isLower offsetLower offsetUpper) where
        mapper :: Exp (Point, Bool, Bool, Int, Int) -> Exp (Maybe DIM1)
        mapper (T5 point isPointUpper isPointLower offsetPointLower offsetPointUpper) = if
          point == p1  then Just_ $ I1 0 else if
          point == p2  then Just_ $ I1 (the countUpper + 1) else if
          isPointUpper then Just_ $ I1 (offsetPointUpper + 1) else if
          isPointLower then Just_ $ I1 (1 + the countUpper + offsetPointLower + 1)
          else Nothing_

      newPoints :: Acc (Vector Point)
      newPoints = permute const defaultValues (destinations !) points ++ p1vector where
        -- Vector (Z :. 1) [p1]
        p1vector = reshape (I1 1) (unit p1)
        newSize = fold1 (+) $ map (\d -> if isJust d then 1 else 0) destinations :: Acc (Scalar Int)
        -- if everything goes alright, the default value should never be used, however the permute function requires to have one
        defaultValues = fill (I1 $ the newSize) undef

      headFlags :: Acc (Vector Bool)
      headFlags = map (\point ->  point == p1 || point == p2) newPoints
  in
  T2 headFlags newPoints


-- The core of the algorithm processes all line segments at once in
-- data-parallel. This is similar to the previous partitioning step, except
-- now we are processing many segments at once.
--
-- For each line segment (p₁,p₂) locate the point furthest from that line
-- p₃. This point is on the convex hull. Then determine whether each point
-- p in that segment lies to the left of (p₁,p₃) or the right of (p₂,p₃).
-- These points are undecided.
--

-- the same as boolToOffset, but then in segments
boolToOffsetSegmented :: Acc (Vector Bool) -> Acc (Vector Bool) -> Acc (Vector Int)
boolToOffsetSegmented headFlags array = map (\i -> i - 1) $ segmentedScanl1 (+) headFlags arrayToInt where
    arrayToInt = map (\b -> if b then 1 else 0) array

partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) =
  T2 newHeadFlags newPoints where
    lines = zip (propagateR headFlags points) (propagateL headFlags points) :: Acc (Vector Line)
    -- distances =                [_, (p0, 15), (p1, 10), (p2, 20), _, (p4, 6), (p5, 3), (p6, 8), (p7, 4), _]
    distances = map (\(T2 line point) -> T2 point (nonNormalizedDistance line point)) (zip lines points) :: Acc (Vector (Point, Int))
    -- furthestPoints = map fst $ [_, (p2, 20), (p2, 20), (p2, 20), _, (p6, 8), (p6, 8), (p6, 8), (p6, 8), _]
    furthestPoints = map fst
            $ propagateR headFlags
            $ segmentedScanl1 (\i1@(T2 _ d1) i2@(T2 _ d2) -> if d1 > d2 then i1 else i2) headFlags distances :: Acc (Vector Point)

    pointData = zip3 lines furthestPoints points :: Acc (Vector (Line, Point, Point))
    isLeftFirstSegment =  map (\(T3 (T2 p1 _) p3 point) -> pointIsLeftOfLine (T2 p1 p3) point) pointData
    isLeftSecondSegment = map (\(T3 (T2 _ p2) p3 point) -> pointIsLeftOfLine (T2 p3 p2) point) pointData

    offsetLeftFirst :: Acc (Vector Int)
    countLeftFirst  :: Acc (Vector Int)
    T2 offsetLeftFirst countLeftFirst = T2 offset count where
        count = map (+1) $ propagateR (shiftHeadFlagsL headFlags) offset
        offset = boolToOffsetSegmented headFlags isLeftFirstSegment

    offsetLeftSecond = boolToOffset isLeftSecondSegment :: Acc (Vector Int)

    -- the relative index (not taking other segments into consideration) in the new vector, if there is any
    destinations :: Acc (Vector (Maybe Int))
    destinations = map mapper (zip6 pointData isLeftFirstSegment isLeftSecondSegment offsetLeftFirst offsetLeftSecond countLeftFirst) where
        mapper :: Exp ((Line, Point, Point), Bool, Bool, Int, Int, Int) -> Exp (Maybe Int)
        mapper (T6 (T3 (T2 p1 _) p3 point) isPointLeftFst isPointLeftSnd offsetPointLeftFst offsetPointLeftSnd countLeftPointFst) = if
          point == p1    then Just_ 0 else if
          point == p3    then Just_ (countLeftPointFst + 1) else if
          isPointLeftFst then Just_ (offsetPointLeftFst + 1) else if
          isPointLeftSnd then Just_ (1 + countLeftPointFst + offsetPointLeftSnd + 1)
          else Nothing_

    indexScan, indexOffset :: Acc (Vector Int)
    indexScan = map (\n -> n - 1) $ scanl1 (+) $ map (\d -> if isJust d then 1 else 0) destinations
    indexOffset = propagateL headFlags indexScan

    realDestinations :: Acc (Vector (Maybe DIM1))
    realDestinations = map
        (\(T2 destination offset) -> maybe Nothing_ (\n -> Just_ $ I1 (n + offset)) destination)
        (zip destinations indexOffset)

    newPoints :: Acc (Vector Point)
    newPoints = permute const defaultValues (realDestinations !) points where
        newSize = the (fold1 (\_ b -> b) indexScan) - 1 :: Exp Int
        -- if everything goes alright, the default value should never be used, however the permute function requires to have one
        defaultValues = fill (I1 newSize) undef

    newHeadFlags :: Acc (Vector Bool) 
    newHeadFlags = undefined




-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull points =
  final where
    initial = initialPartition points
    -- as long as headFlags is not a list of only Trues, the algorithm isnt finished and the loop should be done again
    T2 _ final = awhile
      (\(T2 headFlags _) -> all (\b -> if b then expTrue else expFalse) headFlags)
      partition
      initial

-- Helper functions
-- ----------------

propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL = segmentedScanl1 const

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR = segmentedScanr1 const

shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL vector = scanr const expTrue (tail vector)

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR vector = scanl (\_ b -> b) expTrue (init vector)

segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 f headFlags values = map snd (scanl1 (segmented f) (zip headFlags values))

segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 f headFlags values = map snd (scanr1 (flip $ segmented f) (zip headFlags values))



-- Given utility functions
-- -----------------------

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = if y1 == y2 then y > y2 else nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

segmented :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (bF ? (bV, f aV bV))