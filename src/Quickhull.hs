{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use guards" #-}


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
import Data.Array.Accelerate.Data.Maybe (justs)


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
-- for example: [True, False, False, True, True, False, True] -> [0, _, _, 1, 2, 3, _, 4]
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
        T2 _ count = filter (==expTrue) isUpper
        offset = boolToOffset isUpper

      offsetLower :: Acc (Vector Int)
      countLower  :: Acc (Scalar Int)
      T2 offsetLower countLower = T2 offset count where
        T2 _ count = filter (==expTrue) isLower
        offset = boolToOffset isLower

      -- map each point to the index it will have in the new list, so that in can be thrown in a scatter function
      destinations :: Acc (Vector (Maybe Int))
      destinations = map mapper indexVector where
        mapper index = if
          point == p1 then Just_ 0 else if
          point == p2 then Just_ $ the countUpper + 1 else if
          isUpper !! index then Just_ ((offsetUpper !! index) + 1) else if
          isLower !! index then Just_ (1 + the countUpper + (offsetLower !! index) + 1)
          else Nothing_
            where point = points !! index

        shapePoints = shape points
        indexVector = generate shapePoints indexHead

      newPoints :: Acc (Vector Point)
      newPoints = scatter justDestinations defaultValue clearedPoints ++ p1vector where
        -- the clearedPoints variable must have the same length as the justDestinations in order for scatter to work, 
        -- thus filter out any point that has Nothing on its side
        T2 clearedZippedPoints _ = filter (\(T2 _ destination) -> destination /= Nothing_) (zip points destinations)
        clearedPoints = map fst clearedZippedPoints
        T2 justDestinations _ = justs destinations
        -- Vector (Z :. 1) [p1]
        p1vector = reshape (I1 1) (unit p1)
        -- if everything goes alright, the default value should never be used, however the scatter function requires to have one
        defaultValue = fill (shape clearedPoints) (T2 0 0) 

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
partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) =
  error "TODO: partition"

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
propagateL = error "TODO: propagateL"

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR = error "TODO: propagateR"

shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL vector = scanr const expTrue (tail vector)

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR vector = scanl (\_ b -> b) expTrue (init vector)

segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 = error "TODO: segmentedScanl1"

segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 = error "TODO: segmentedScanr1"


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