{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}

module LeavesBelow where

import           Control.Applicative
import           Control.Monad
import           Data.Set            (Set)
import qualified Data.Set            as Set
import           Data.Traversable    (Traversable (..))
import           System.Directory    (getTemporaryDirectory)
import           System.FilePath     ((</>))
import           System.IO.Unsafe
import           System.Process      (system)

import           Data.Foldable


import           AG
import           Dag.AG
import           Dag.Internal
import           Dag.Render





data IntTreeF a = Leaf Int | Node a a
  deriving (Eq, Show)


data IntTree = Leaf' Int | Node' IntTree IntTree
  deriving (Eq, Show)

iNode x y = In (Node x y)
iLeaf i = In (Leaf i)


leavesBelow :: Int -> IntTree -> Set Int
leavesBelow d (Leaf' i)
    | d <= 0                 =  Set.singleton i
    | otherwise              =  Set.empty
leavesBelow d (Node' t1 t2)  =
    leavesBelow (d-1) t1 `Set.union` leavesBelow (d-1) t2


t = let a = Node' (Node' (Leaf' 2)
                         (Leaf' 3))
                  (Leaf' 4)
    in Node' a a

instance Foldable IntTreeF where
    foldr _ z (Leaf _) = z
    foldr f z (Node x y) = x `f` (y `f` z)

instance Functor IntTreeF where
    fmap _ (Leaf i) = Leaf i
    fmap f (Node x y) = Node (f x) (f y)

instance Traversable IntTreeF where
    mapM _ (Leaf i) = return (Leaf i)
    mapM f (Node x y) = liftM2 Node (f x) (f y)

    traverse _ (Leaf i) = pure (Leaf i)
    traverse f (Node x y) = liftA2 Node (f x) (f y)


leavesBelowI :: Inh IntTreeF atts Int
leavesBelowI (Leaf i)      = o
leavesBelowI (Node t1 t2)  = t1 |-> d' & t2 |-> d'
            where d' = above - 1

leavesBelowS :: (Int :< atts) => Syn IntTreeF atts (Set Int)
leavesBelowS (Leaf i)
    | (above :: Int) <= 0  =  Set.singleton i
    | otherwise            =  Set.empty
leavesBelowS (Node t1 t2)  =  below t1 `Set.union` below t2

leavesBelow' :: Int -> Tree IntTreeF -> Set Int
leavesBelow' d = runAG leavesBelowS leavesBelowI (const d)
-- pour tous mes fils numerotes je renvois la constante d

leavesBelowG :: Int -> Dag IntTreeF -> Set Int
leavesBelowG d = runAGDag min leavesBelowS leavesBelowI (const d)

---

tf  :: Tree IntTreeF
tf = let a = iNode (iNode (iLeaf 2)
                          (iLeaf 3))
                   (iLeaf 4)
     in iNode a a

dagtf  :: Dag IntTreeF
dagtf = unsafePerformIO $ reifyDag tf

intTreeTestDAG1 = leavesBelowG 3 dagtf
intTreeTestDAG2 = leavesBelow' 3 (unravelDag dagtf)
---


it1 :: Tree IntTreeF
it1 = iNode (iNode x (iLeaf 10)) x
    where x = iNode y y
          y = iLeaf 20
          z = iLeaf 20

i1 :: Dag IntTreeF
i1 = unsafePerformIO $ reifyDag it1


it2 :: Tree IntTreeF
it2 = iNode x (iNode (iLeaf 5) x)
    where x = iNode (iNode (iLeaf 24) (iLeaf 3)) (iLeaf 4)

i2 :: Dag IntTreeF
i2 = unsafePerformIO $ reifyDag it2


intTreeTestG1 = leavesBelowG 3 i1
intTreeTestT1 = leavesBelow' 3 (unravelDag i1)


intTreeTestG2 = leavesBelowG 3 i2
intTreeTestT2 = leavesBelow' 3 (unravelDag i2)


--

instance ShowConstr IntTreeF
  where
    showConstr (Leaf i)     = "Leaf " ++ show i
    showConstr (Node _ _)   = "Node "

renderDag2 ::  (ShowConstr f, Traversable f) =>  Dag f -> IO ()
renderDag2 dag = do
    tmpd <- getTemporaryDirectory
    let tmpf = tmpd </> "523452345234"
    renderDag dag tmpf
    system $ "dot -Tsvg " ++ tmpf ++ " -o last.svg"
    return ()

di1 = renderDag2 i1
