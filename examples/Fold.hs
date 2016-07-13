{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE UnicodeSyntax    #-}


module Fold where

import           Control.Applicative
import           Control.Monad
import           Data.Set            (Set)
import qualified Data.Set            as Set
import           Data.Traversable    (Traversable (..))
import           System.IO.Unsafe

import           Data.Foldable       hiding (fold)

import           AG
import           Dag.AG
import           Dag.Internal

type Algebra f c = f c → c

fold :: Functor f ⇒ Algebra f c → Tree f → c
fold alg (In t) = alg (fmap (fold alg) t)

algS :: ∀ f c atts. (Functor f, Traversable f, c :< atts) => Algebra f c → Syn f atts c
algS alg (fa ∷ f a) = alg ((below <$> fa) ∷ f c)  -- below ∷ (?below ∷ a → as, c ∈ as) ⇒ a → c


-- fold ne peut exprimer leaves below
algI ::  (Functor f, Traversable f) ⇒ Inh f atts Int
algI ft   = o

fold' ∷  (Functor f, Traversable f) ⇒ Algebra f c → Tree f → c
fold' alg =  runAG (algS alg) algI (const (0 ∷ Int))

data IntTreeF a = Leaf Int | Node a a
  deriving (Eq, Show)

iNode x y = In (Node x y)
iLeaf i = In (Leaf i)

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

-- fold ne peut exprimer leaves below
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
-- cf signature de runAG dans AG.hs

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



-- les competences d'appui, de coordination ou de complement
