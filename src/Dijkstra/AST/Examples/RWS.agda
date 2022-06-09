{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Examples.RWS where

open import Data.Product      using (_×_ ; _,_)
open import Dijkstra.AST.Core
open import Haskell.Prelude
open import Relation.Binary.PropositionalEquality

module Example1 (A : Set) where

  open import Data.Nat         renaming (ℕ to Nat) using (_+_ ; suc ; zero)
  open import Dijkstra.AST.RWS A A (List A)
  open        ASTPredTrans     RWSPT
  open        RWSSyntax

  sucn≡n+1 : ∀ (n : Nat) -> suc n ≡ n + 1
  sucn≡n+1  zero   = refl
  sucn≡n+1 (suc n) = cong suc (sucn≡n+1 n)

  prog : RWS (List A)
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
  ProgPost (_ , si) (a , so , w) = length  a ≡ length so + 1
                                 × length so ≡ length si + 1
                                 × length  w ≡ 3

  progPost : ∀ i -> ProgPost i (runRWS prog i)
  progPost (e , s) with runRWS prog (e , s)
  ... | (a , st , wr)
    rewrite sucn≡n+1 (length s)
    = refl , refl , refl

  -- Proving this WP is straightforward compared to sum types (e.g., Maybe, Either).
  -- When proving sum types, it is necessary to break the proof obligations down into cases.
  -- With this usage of RWS, there are no cases. Here, an equality (e.g., r₅≡1∷si)
  -- established by the RWS bind definition is used.
  progPostWP : ∀ i -> predTrans prog (ProgPost i) i
  progPostWP (c , si) _ _ _ _ _ _ _ _ _ _ r₅ r₅≡1∷si _ _
    rewrite r₅≡1∷si | sucn≡n+1 (length si)
    = refl , refl , refl

  -- C-c C-n
  -- Example1.runProg
  -- returns : λ A a → a ∷ a ∷ [] , a ∷ [] , a ∷ a ∷ a ∷ []
  runProg : A -> (List A × List A × List A)
  runProg a = runRWS prog (a , [])
