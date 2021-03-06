module Test where

import Language.Haskell.Liquid.ProofCombinators
import SlimPrelude
import CircularList

import Prelude hiding (length, 
                        (++), 
                        reverse,
                        any
                        )

{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}


-- data CList a = Empty
--              | CList [a] a [a]

{-@ reflect toList @-}
toList :: CList a -> [a]
toList Empty = []
toList (CList l f r) = f : (r ++ (reverse l))


{-@ reflect eqToList @-}
eqToList ::  CList Int -> CList Int -> Bool
eqToList a b = toList a == toList b

{-@ reflect =*= @-}
{-@ infix 4 =*= @-}
(=*=) :: CList Int -> CList Int -> Bool
x =*= y = (any (eqToList x) (toList (singleton y)))

{-@ reflect lemma_refl @-}
lemma_refl :: Bool
lemma_refl = Empty =*= Empty

{-@ ple lemma_refl_proof @-}
{-@ lemma_refl_proof ::  { lemma_refl  } @-}
lemma_refl_proof :: Proof
lemma_refl_proof = lemma_refl
                *** QED

