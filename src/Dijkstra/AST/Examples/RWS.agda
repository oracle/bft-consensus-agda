{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Examples.RWS where

open import Data.Product      using (_×_ ; _,_)
open import Haskell.Prelude
open import Relation.Binary.PropositionalEquality

module Example1 (A : Set) where

  open import Data.Nat         renaming (ℕ to Nat) using (_+_ ; suc ; zero)
  open import Dijkstra.AST.RWS A A (List A)

  prog : RWSAST (List A)
  prog = do
    ev  <- ask
    tell   (ev ∷ [])
    st  <- gets (λ x -> x)
    tell   (ev ∷ [])
    _   <- puts λ s -> (ev ∷ s)
    st' <- gets (λ x -> x)
    tell   (ev ∷ [])
    return (ev ∷ st')

  ProgPost : (A × List A) -> (List A × List A × List A) -> Set
  ProgPost (_ , si) (a , so , w) = length  a ≡ 1 + length so
                                 × length so ≡ 1 + length si
                                 × length  w ≡ 3

  progPost : ∀ i -> ProgPost i (runRWSAST prog i)
  progPost (e , s) with runRWSAST prog (e , s)
  ... | (a , st , wr)
      = refl , refl , refl

  -- Proving this WP is straightforward compared to sum types (e.g., Maybe, Either).
  -- When proving sum types, it is necessary to break the proof obligations down into cases.
  -- With this usage of RWS, there are no cases. Here, an equality (e.g., r₅≡1∷si)
  -- established by the RWS bind definition is used.
  progPostWP : ∀ i -> predTrans prog (ProgPost i) i
  progPostWP (c , si) _ _ _ _ _ _ _ _ _ _ r₅ r₅≡1∷si _ _
    rewrite r₅≡1∷si
    = refl , refl , refl

  -- C-c C-n
  -- Example1.runProg
  -- returns : λ A a → a ∷ a ∷ [] , a ∷ [] , a ∷ a ∷ a ∷ []
  runProg : A -> (List A × List A × List A)
  runProg a = runRWSAST prog (a , [])
