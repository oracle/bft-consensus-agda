{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Data.Nat
import      Level
open import Util.Prelude
open import Dijkstra.AST.Branching
open import Dijkstra.AST.Core
open import Dijkstra.AST.Maybe

module  Dijkstra.AST.Maybe.Examples.Branching where

  open ASTTypes MaybeTypes
  open ASTPredTrans MaybePT
  open ASTExtension 
  open Syntax

  dblNonZero : ℕ → ∀ {ℓ} → Level.Lift ℓ Bool → MaybeDExt ℕ
  dblNonZero _ (lift true)  = ASTop (Left Maybe-bail) λ ()
  dblNonZero n (lift false) = ASTreturn (2 * n)

  -- A program that includes branching in MaybeD
  branchingProg : ℕ → MaybeDExt ℕ
  branchingProg n = ASTop (Right (BCif (toBool (n ≟ℕ 0) ))) (dblNonZero n)

  -- A postcondition requiring that it can fail only if n is zero, and if it succeeds, the result is
  -- greater than the argument
  bpPost : ℕ → Post ℕ
  bpPost n (just n') = n' > n
  bpPost n nothing   = n ≡ 0

  dblNZ> : ∀ {n} → n ≢ 0 → n < n + (n + 0)
  dblNZ> {0} nz     = ⊥-elim (nz refl)
  dblNZ> {suc n} nz rewrite +-identityʳ (suc n) = m<m+n _ 0<1+n

  -- The weakest precondition for bpPost holds
  branchingProgWorks : (n : ℕ) → (i : Input)
                       → ASTPredTrans.predTrans MaybePTExt (branchingProg n) (bpPost n) i
  proj₁ (branchingProgWorks n i) isTrue  = toWitnessT isTrue
  proj₂ (branchingProgWorks n i) isFalse = dblNZ> (toWitnessF isFalse)

  -- And therefore, the result of running the program satisfies the postcondition
  prop : (n : ℕ) → (i : Input) → (bpPost n) (runMaybeExt (branchingProg n) i)
  prop n i = ASTSufficientPT.sufficient MaybeSufExt (branchingProg n) (bpPost n) i (branchingProgWorks n i)
