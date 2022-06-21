{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
module Dijkstra.AST.Examples.PaperIntro (Ev Wr St : Set) where

open import Dijkstra.AST.Prelude
open import Dijkstra.AST.RWS Ev Wr St
open import Relation.Binary.PropositionalEquality

-- The example in the paper
prog : (St → Maybe Wr) → RWSAST Unit
prog f = pass inner
  where inner : RWSAST (Unit × (List Wr → List Wr))
        inner = do
          m ← gets f
          maybeAST (λ w → do tell (w ∷ [])
                             return (unit , λ _ → []))
                   (return (unit , (λ x → x ++ x)))
                   m

ProgPost : (Ev × St) → (Unit × St × List Wr) → Set
ProgPost (_ , s1) (_ , s2 , o) = s1 ≡ s2 × 0 ≡ length o

-- Here we prove that, for any f and i, the postcondition holds of the result of running (prog f)
-- on i.  The proof is deceptively simple, as explained after the proof.
progPost : ∀ f i → ProgPost i (runRWSAST (prog f) i)
progPost f (_ , s) with f s
... | nothing = refl , refl
... | just _  = refl , refl

{- We start with:

  progPost : ∀ f i → ProgPost i (runRWSAST (prog f) i)
  progPost f i = ?

  -- The goal, of course, is: ProgPost i (runRWSAST (prog f) i)
  -- But if we expand this (C-u C-u C-c C-,), we see:

  Goal: Data.Product.Σ
        (proj₂ i ≡
         proj₁
         (proj₂
          (Dijkstra.AST.Core.ASTOpSem.runAST RWSBase.RWSOpSem
           (Dijkstra.AST.Branching.ASTExtension.unextend RWSBase.RWSOps
            (Dijkstra.AST.Core.AST.ASTop
             (Right (Dijkstra.AST.Branching.BranchCmd.BCmaybe (f (proj₂ i))))
             (λ { (Level.lift nothing)
                    → Dijkstra.AST.Core.AST.ASTreturn (unit , (λ x → x ++ x))
                ; (Level.lift (just a))
                    → Dijkstra.AST.Core.AST.ASTbind
                      (Dijkstra.AST.Core.AST.ASTop (Left (RWSBase.RWStell (a ∷ []) refl))
                       (λ ()))
                      (λ _ → Dijkstra.AST.Core.AST.ASTreturn (unit , (λ _ → [])))
                })))
           (proj₁ i , proj₂ i))))
        (λ x →
           0 ≡
           foldr (λ _ → Agda.Builtin.Nat.Nat.suc) 0
           (proj₂
            (proj₁
             (Dijkstra.AST.Core.ASTOpSem.runAST RWSBase.RWSOpSem
              (Dijkstra.AST.Branching.ASTExtension.unextend RWSBase.RWSOps
               (Dijkstra.AST.Core.AST.ASTop
                (Right (Dijkstra.AST.Branching.BranchCmd.BCmaybe (f (proj₂ i))))
                (λ { (Level.lift nothing)
                       → Dijkstra.AST.Core.AST.ASTreturn (unit , (λ x₁ → x₁ ++ x₁))
                   ; (Level.lift (just a))
                       → Dijkstra.AST.Core.AST.ASTbind
                         (Dijkstra.AST.Core.AST.ASTop (Left (RWSBase.RWStell (a ∷ []) refl))
                          (λ ()))
                         (λ _ → Dijkstra.AST.Core.AST.ASTreturn (unit , (λ _ → [])))
                   })))
              (proj₁ i , proj₂ i)))
            (proj₂
             (proj₂
              (Dijkstra.AST.Core.ASTOpSem.runAST RWSBase.RWSOpSem
               (Dijkstra.AST.Branching.ASTExtension.unextend RWSBase.RWSOps
                (Dijkstra.AST.Core.AST.ASTop
                 (Right (Dijkstra.AST.Branching.BranchCmd.BCmaybe (f (proj₂ i))))
                 (λ { (Level.lift nothing)
                        → Dijkstra.AST.Core.AST.ASTreturn (unit , (λ x₁ → x₁ ++ x₁))
                    ; (Level.lift (just a))
                        → Dijkstra.AST.Core.AST.ASTbind
                          (Dijkstra.AST.Core.AST.ASTop (Left (RWSBase.RWStell (a ∷ []) refl))
                           (λ ()))
                          (λ _ → Dijkstra.AST.Core.AST.ASTreturn (unit , (λ _ → [])))
                    })))
               (proj₁ i , proj₂ i))))))

  -- This is quite unwieldy, and it's very challenging to look at this and determine that
  -- we need to do 'with f s' (after refining the input i to (_ , s)), to get the two cases to
  -- prove.  And this is for a small, relatively simple program that is all in scope, so we have
  -- no need to prove and invoke properties about functions called within the program.

  -- The proof via predicate transformer semantics and sufficiency that follow demonstrates how
  -- much easier the framework makes it to prove this property.

-}

-- See below for step-by-step development and explanation of this proof
progPostWP : ∀ f i → predTrans (prog f) (ProgPost i) i
proj₁ (progPostWP _ _ _ refl) _ = λ where          _ refl → refl , refl
proj₂ (progPostWP _ _ _ refl) j = λ where _ _ refl _ refl → refl , refl

{-
  -- We start with:

  progPostWP : ∀ f i → predTrans (prog f) (ProgPost i) i
  progPostWP f i = {!!}

  -- In the following, each time we make a step, the goal in each hole is much more manageable and
  -- understandable than the unwieldy one shown above for the direct approach.

  -- C-c C-c in *empty* hole, press enter to split on result

  progPostWP f i r x = {!!}

  -- C-c C-c with x in the hole

  progPostWP f i .(f (proj₂ i)) refl = {!!}

  -- C-c C-c in *empty* hole, press enter to split on result

  proj₁ (progPostWP f i .(f (proj₂ i)) refl) = {!!}
  proj₂ (progPostWP f i .(f (proj₂ i)) refl) = {!!}

  -- C-c C-r in *each* hole

  proj₁ (progPostWP f i .(f (proj₂ i)) refl) = λ        x o' x₁ → {!!}
  proj₂ (progPostWP f i .(f (proj₂ i)) refl) = λ j x r x₁ o' x₂ → {!!}

  -- x₁ : o' ≡  ([] ++ []) ++ [] ++ [], change to λ where ... refl to rewrite it,
  -- and similarly for x₂ : o' ≡ []

  proj₁ (progPostWP f i .(f (proj₂ i)) refl) = λ where       x  o' refl → {!!}
  proj₂ (progPostWP f i .(f (proj₂ i)) refl) = λ where j x r x₁ o' refl → {!!}

  C-c C-r in each hole splits each goal into a product

  proj₁ (progPostWP f i .(f (proj₂ i)) refl) = λ where        x o' refl → {!!} , {!!}
  proj₂ (progPostWP f i .(f (proj₂ i)) refl) = λ where j x r x₁ o' refl → {!!} , {!!}

  C-c C-r in each hole completes the proof

  proj₁ (progPostWP f i .(f (proj₂ i)) refl) = λ where        x o' refl → refl , refl
  proj₂ (progPostWP f i .(f (proj₂ i)) refl) = λ where j x r x₁ o' refl → refl , refl

  -- The version above is the same thing, hiding things that don't need to be
  -- exposed.

-}

-- As we have proved that the precondition determined by predTrans (prog f) (ProgPost i) holds for
-- all i, we can use sufficiency to prove that the postcondition holds after running the program
-- for any input
progPost' : ∀ f i → ProgPost i (runRWSAST (prog f) i)
progPost' f i = sufficient (prog f) (ProgPost i) i (progPostWP f i) 
