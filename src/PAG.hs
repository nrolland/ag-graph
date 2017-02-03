{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE UnicodeSyntax       #-}


--------------------------------------------------------------------------------
-- |
-- Module      :  PAG
-- Copyright   :  (c) 2014 Patrick Bahr, Emil Axelsson
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements recursion schemes derived from attribute
-- grammars. The variant implemented in this module, called parametric
-- attribute grammars, generalises both attribute grammars and
-- attribute grammars with rewrite function (as implemented in
-- "AG").
--
--------------------------------------------------------------------------------

module PAG
    ( runPAG
    , module I
    )  where

import           Mapping        as I
import           PAG.Internal
import qualified PAG.Internal   as I hiding (explicit)
import           PAG.Projection as I
import           Tree           as I




-- | This function runs a parametric attribute grammar on a term. The
-- result is the (combined) synthesised attribute at the root of the
-- term.

runPAG :: ∀ f u d g . (Traversable f, Functor g, Functor d, Functor u)
          => Syn' f (u :*: d) u g  -> Inh' f (u :*: d) d g  -> (forall a . u a -> d (Free g a))  -> Tree f -> u (Tree g)
runPAG (up    ::  Syn' f (u :*: d) u g)  -- ^ semantic function of synthesised attributes
       (down  ::  Inh' f (u :*: d) d g)   -- ^ semantic function of inherited attributes
       (dinit ::  ∀ a . u a -> d (Free g a))   -- ^ input term
       (t     ::  Tree f)
  = uFin ::  u (Tree g)
  where
    uFin = run dFin t
    dFin :: d (Tree g) = appCxt <$> ((dinit uFin) :: d (Free g (Tree g)))
    run  :: d (Tree g) -> Tree f -> u (Tree g)
    run d (In t) = u where
        t' = bel <$> number t
        bel (Numbered i s) =
            let d' = lookupNumMap d i m
            in Numbered i (run d' s :*: d')
        m :: NumMap ((:*:) u d (Tree g)) (d (Tree g))  = fmap (fmap appCxt) $
               (explicit down (u :*: d) unNumbered t' :: NumMap ((:*:) u d (Tree g)) (d (Free g (Free g Zero))))
        u = fmap appCxt $ explicit up (u :*: d) unNumbered t'
