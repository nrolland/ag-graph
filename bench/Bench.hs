{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Monoid

import Criterion.Main
import Criterion.Config
import Control.DeepSeq

import AG
import Graph
import Paper



--------------------------------------------------------------------------------
-- * Setup
--------------------------------------------------------------------------------

class Functor f => NFDataF f
  where
    rnfF :: NFData a => f a -> ()

instance NFDataF f => NFData (Tree f)
  where
    rnf (In f) = rnfF f

instance NFDataF f => NFData (Graph f)
  where
    rnf (Graph r es n) = rnf r `seq` rnf n `seq` rnf (fmap rnfF es)

instance NFDataF IntTreeF
  where
    rnfF (Leaf l)   = rnf l `seq` ()
    rnfF (Node a b) = rnf a `seq` rnf b `seq` ()

expTree :: Int -> Tree IntTreeF
expTree 1 = In $ Leaf 10
expTree n = In $ Node (expTree (n-1)) (expTree (n-1))

expGraph :: Int -> Graph IntTreeF
expGraph = termTree . expTree

linearGraph :: Int -> Graph IntTreeF
linearGraph n = mkGraph 0 $
    [(k, Node (k+1) (k+1)) | k <- [0..n-2] ] ++ [(n-1, Leaf 10)]



--------------------------------------------------------------------------------
-- * Reduce
--------------------------------------------------------------------------------

-- This benchmark is designed to be as simple as possible: only integer
-- attributes and simple semantic functions. This is to make be able to test the
-- efficiency of the run functions themselves.

newtype Value = Value Int deriving (Eq, Ord, Show, Num, Enum)
newtype Depth = Depth Int deriving (Eq, Ord, Show, Num, Enum)

value :: (Depth :< a) => Syn IntTreeF a Value
value (Leaf l) = Value (l+d)
  where
    Depth d = above
value (Node a b) = max (below a) (below b)

depth :: Inh IntTreeF a Depth
depth (Node a b) = a |-> d & b |-> d
  where
    d = above+1
depth _ = o

reduce :: Tree IntTreeF -> Int
reduce = fromEnum . runAG value depth 0

reduceG :: Graph IntTreeF -> Int
reduceG = fromEnum . runAGGraph max value depth 0

reduce_expTree n = bgroup "expTree"
    [bench (show n) $ nf reduce $ expTree n | n <- [4..n]]
  -- Grows exponentially

reduce_expGraph n = bgroup "expGraph"
    [bench (show n) $ nf reduceG $ expGraph n | n <- [4..n]]
  -- Grows exponentially. The overhead compared to `reduce` is about 6x for
  -- trees of size up to 2^16.

reduce_linearGraph n = bgroup "linearGraph"
    [bench (show n) $ nf reduceG $ linearGraph n | n <- [4..n]]
  -- Grows linearly

reduce_linearGraphBig n = bgroup "linearGraphBig"
    [bench (show n) $ nf reduceG $ linearGraph n | n <- [10,20..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`

conf name = defaultConfig
    { cfgReport      = Last $ Just $ "reports/" ++ name ++ ".html"
    , cfgSummaryFile = Last $ Just $ "reports/" ++ name ++ ".csv"
    }



--------------------------------------------------------------------------------
-- * Repmin
--------------------------------------------------------------------------------

-- The results for `repmin` are quite consistent with those for `reduce`. One
-- important difference is that `repmin` produces a tree as result, which means
-- that simply forcing a bit result takes some time.

repmin_expTree n = bgroup "expTree"
    [bench (show n) $ nf repmin $ expTree n | n <- [4..n]]
  -- Grows exponentially

repmin_expGraph n = bgroup "expGraph"
    [bench (show n) $ nf repminG $ expGraph n | n <- [4..n]]
  -- Grows exponentially. The overhead compared to `repmin` is about 5x for
  -- trees of size up to 2^16.

repmin_expGraph' n = bgroup "expGraph'"
    [bench (show n) $ nf repminG' $ expGraph n | n <- [4..n]]
  -- Grows exponentially. The overhead compared to `repmin` is about 70x for
  -- trees of size up to 2^12.

repmin_linearGraph n = bgroup "linearGraph"
    [bench (show n) $ nf repminG $ linearGraph n | n <- [4..n]]

repmin_linearGraph' n = bgroup "linearGraph'"
    [bench (show n) $ nf repminG' $ linearGraph n | n <- [4..n]]
  -- Grows linearly

repmin_linearGraphBig n = bgroup "linearGraphBig"
    [bench (show n) $ nf repminG' $ linearGraph n | n <- [10,20..n]]
  -- Grows linearly even for sizes that are out of reach for `repmin`

main = do
    defaultMainWith (conf "reduce_overhead_expTree")     (return ()) [reduce_expTree        16]
    defaultMainWith (conf "reduce_overhead_expGraph")    (return ()) [reduce_expGraph       16]
    defaultMainWith (conf "reduce_sharing_expTree")      (return ()) [reduce_expTree        12]
    defaultMainWith (conf "reduce_sharing_expGraph")     (return ()) [reduce_expGraph       12]
    defaultMainWith (conf "reduce_sharing_linearGraph")  (return ()) [reduce_linearGraph    12]
    defaultMainWith (conf "reduce_big_linearGraph")      (return ()) [reduce_linearGraphBig 200]

    defaultMainWith (conf "repmin_overhead_expTree")     (return ()) [repmin_expTree        16]
    defaultMainWith (conf "repmin_overhead_expGraph")    (return ()) [repmin_expGraph       16]
    defaultMainWith (conf "repmin_overhead_expGraph'")   (return ()) [repmin_expGraph'      12]  -- OBS only up to 12
    defaultMainWith (conf "repmin_sharing_expTree")      (return ()) [repmin_expTree        12]
    defaultMainWith (conf "repmin_sharing_expGraph")     (return ()) [repmin_expGraph       12]
    defaultMainWith (conf "repmin_sharing_linearGraph")  (return ()) [repmin_linearGraph    12]
    defaultMainWith (conf "repmin_sharing_linearGraph'") (return ()) [repmin_linearGraph    12]
    defaultMainWith (conf "repmin_big_linearGraph")      (return ()) [repmin_linearGraphBig 200]

