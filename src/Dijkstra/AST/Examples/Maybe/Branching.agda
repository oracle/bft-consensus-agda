{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Data.Nat
import      Level
open import Util.Prelude hiding (bail)
open import Dijkstra.AST.Branching
open import Dijkstra.AST.Core
open import Dijkstra.AST.Maybe

module Dijkstra.AST.Examples.Maybe.Branching where

open ASTTypes MaybeTypes
open ASTPredTrans MaybePT
open ASTExtension

module Example-if (n : ℕ) where
  -- First we specify the behaviour we want via a postcondition requiring that the program can fail
  -- only if n is zero, and if it succeeds, the n is non-zero and the result is 2 * n
  bpPost : Post ℕ
  bpPost nothing   = n ≡ 0
  bpPost (just n') = 0 < n × n' ≡ 2 * n

  module Raw where
    -- A program that includes branching in MaybeD, intended to satify the specification
    -- established by bpPost
    branchingProg : MaybeDExt ℕ
    branchingProg = ASTop (Right (BCif (toBool (n ≟ℕ 0) )))
                          (λ { (lift false) → ASTreturn (2 * n)
                             ; (lift true)  → ASTop (Left Maybe-bail) λ () })

    -- The weakest precondition for bpPost holds
    branchingProgWorks : (i : Input)
                         → ASTPredTrans.predTrans MaybePTExt branchingProg bpPost i
    proj₁ (branchingProgWorks _) isTrue  =           toWitnessT isTrue
    proj₂ (branchingProgWorks _) isFalse = (n≢0⇒n>0 (toWitnessF isFalse)) , refl

    -- And therefore, the result of running the program satisfies the postcondition
    prop : (i : Input) → bpPost (runMaybeExt branchingProg i)
    prop i =
      ASTSufficientPT.sufficient MaybeSufExt branchingProg bpPost i (branchingProgWorks i)

  module Prettier where
    open BranchingSyntax MaybeOps
    open MaybeBranchingSyntax

    -- Same program with nicer syntax using ifAST, bail and return
    branchingProg : MaybeDExt ℕ
    branchingProg = ifAST ⌊ n ≟ℕ 0 ⌋
                    then bail
                    else (return (2 * n))

    --  Note that the same proof works for both versions (as they are equivalent)
    branchingProgWorks : (i : Input)
                         → ASTPredTrans.predTrans MaybePTExt branchingProg bpPost i
    proj₁ (branchingProgWorks i) isTrue  = toWitnessT isTrue
    proj₂ (branchingProgWorks i) isFalse = (n≢0⇒n>0 (toWitnessF isFalse)) , refl

    prop : (i : Input) → bpPost (runMaybeExt branchingProg i)
    prop i = ASTSufficientPT.sufficient MaybeSufExt branchingProg bpPost i (branchingProgWorks i)
