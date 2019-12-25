{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE UnicodeSyntax       #-}

{-# LANGUAGE ScopedTypeVariables #-}



module Fold where

import           Control.Applicative
import           Control.Monad
import           Data.Set            (Set)
import qualified Data.Set            as Set
import           Data.Traversable    (Traversable (..))
import           System.IO.Unsafe

import           Data.Foldable       hiding (fold)
import           Data.Map            hiding (fold)
import           Data.Void

import           AG
import           Dag.AG
import           Dag.Internal

import           Data.Constraint
import           Data.Proxy
import           Projection.TypeFam

type Algebra f c = f c → c


t1 ∷ Dict (Eq (Int))
t1 = Dict


fold :: Functor f ⇒ Algebra f c → Tree f → c
fold alg (In t) = alg (fmap (fold alg) t)

algS :: ∀ f c atts. (Functor f, Traversable f, c :< atts) => Algebra f c → Syn f atts c
algS alg (fa ∷ f a) = alg ((below <$> fa) ∷ f c)  -- below ∷ (?below ∷ a → as, c ∈ as) ⇒ a → c

-- fold ne peut exprimer leaves below
algI ::  ∀ f c atts. (Functor f, Traversable f) ⇒ Inh f atts Int
algI ft  = o


-- le type doit etre pleinement applique sinon la recherche d'instance ne marche pas
fold' ∷  (Functor f, Traversable f, Ord c, c :< (c,Int), Int :< (c,Int)) ⇒ Algebra f c → Tree f → c
fold' alg =  runAG (algS alg) algI (const (0 ∷ Int))


-- | This function runs an attribute grammar on a term with no inherited attribute
-- the (combined) synthesised attribute at the root of the term.
runAGF :: forall f s . Traversable f
      => Syn' f s s -- ^ semantic function of synthesised attributes
      -> Tree f         -- ^ input tree
      -> s
runAGF syn  t = sFin where
    sFin = run t
    run :: Tree f -> s
    run (In t) = s where
        --bel (Numbered n c) =  Numbered n (run c) -- je recurse avec le type numbered
        --t'  = bel <$> number t   -- j'enrichis le type avec numbered
        --s   = explicit syn s unNumbered t'  -- pour delivrer le resultat final, j'enleve l'enrichissement
        t' = run <$> t -- je recurse sans enrichissment
        s   = explicit syn s id t' -- je delivre le resultat

fold2 ∷  (Functor f, Traversable f, Ord c) ⇒ Algebra f c → Tree f → c
fold2 alg =  runAGF (algS alg)


p ∷ Dict (Int :< (Char,Int))
p = Dict

-- cf TypeFam.hs qThe first argument of ‘Dict’ should have kind ‘Constraint’, but
-- ‘Elem Int (Char, Int)’ has kind ‘RPos’

--p1 ∷ Dict (Elem Int (Char,Int))
--p1 = Dict

-- :k GetPointer
-- GetPointer :: RPos -> * -> * -> ghc-prim-0.4.0.0:GHC.Prim.Constraint

p2 ∷ Dict (GetPointer (Elem Int (Char,Int)) Int (Char,Int))
p2 = Dict

--   No instance for (GetPointer
--                       (Ch (Elem Int c) ('Found 'Here))
--                       Int (c, Int))
--p3 ∷ ∀ c. Dict (GetPointer (Elem Int (c,Int)) Int (c,Int))
--p3 = Dict

-- on calcule bien Elem Int (c,Int) vers (Ch (Elem Int c) ('Found 'Here))
-- pourquoi pas ensuite appliquer Ch ?? vers Found (Right 'Here) parce que le
-- type doit etre completement applique, cf limitation evoquee dans le papier



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
