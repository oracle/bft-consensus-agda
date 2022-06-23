{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
module Dijkstra.AST.Examples.PaperIntro (Ev Wr St : Set) where

open import Data.List                   using (List ; length ; [] ; _∷_ ; _++_)
open import Data.Maybe                  using (Maybe ; maybe ; just ; nothing)
open import Data.Product                using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.NonEta            using (Unit; unit)
open import Dijkstra.AST.RWS Ev Wr St
-- TODO-2: We should not be depending on things in the Haskell namespace here as Dijkstra.*
-- should be independent of things outside the Dijkstra namespace
open import Haskell.Prelude             using (_>>_ ; _>>=_ ; return)
open import Relation.Binary.PropositionalEquality

-- The example in the paper
prog : (St → Maybe Wr) → RWSAST Unit
prog g = pass inner
  where inner : RWSAST (Unit × (List Wr → List Wr))
        inner = do
          m ← gets g
          maybeAST (λ w → do tell (w ∷ [])
                             return (unit , λ _ → []))
                   (return (unit , (λ x → x ++ x)))
                   m

ProgPost : (Ev × St) → (Unit × St × List Wr) → Set
ProgPost (_ , s1) (_ , s2 , o) = s1 ≡ s2 × 0 ≡ length o

-- Here we prove directly (i.e., *without* using our framework) that, for any f and i, the
-- postcondition holds of the result of running (prog f) on i.  The proof is deceptively simple, as
-- explained after the proof.
progPost : ∀ g i → ProgPost i (runRWSAST (prog g) i)
progPost g (_ , s) with g s
... | nothing = refl , refl
... | just _  = refl , refl

{- We start with:

  progPost : ∀ g i → ProgPost i (runRWSAST (prog g) i)
  progPost g i = ?

  -- The goal, of course, is: ProgPost i (runRWSAST (prog g) i)
  -- But if we expand this (C-u C-u C-c C-,), we see:

  Goal: Data.Product.Σ
        (proj₂ i ≡
         proj₁
         (proj₂
          (Dijkstra.AST.Core.ASTOpSem.runAST RWSBase.RWSOpSem
           (Dijkstra.AST.Branching.ASTExtension.unextend RWSBase.RWSOps
            (Dijkstra.AST.Core.AST.ASTop
             (Right (Dijkstra.AST.Branching.BranchCmd.BCmaybe (g (proj₂ i))))
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
                (Right (Dijkstra.AST.Branching.BranchCmd.BCmaybe (g (proj₂ i))))
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
                 (Right (Dijkstra.AST.Branching.BranchCmd.BCmaybe (g (proj₂ i))))
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
  -- we need to do 'with g s' (after refining the input i to (_ , s)), to get the two cases to
  -- prove.  And this is for a small, relatively simple program that is all in scope, so we have
  -- no need to prove and invoke properties about functions called within the program.

  -- The proof via predicate transformer semantics and sufficiency that follow demonstrates how
  -- much easier the framework makes it to prove this property.

-}

-- Here is an alternative proof, which uses our framework to guide the proof development.
-- See below for a step-by-step explanation.
progPostWP : ∀ g i → predTrans (prog g) (ProgPost i) i
proj₁ (progPostWP _ _ _ _) _ _ _ _ _ refl = refl , refl
proj₂ (progPostWP _ _ _ _)   _     _ refl = refl , refl

{- TUTORIAL: Here we explain step-by-step how the framework facilitates the above proof.

  -- We start with:

  progPostWP : ∀ g i → predTrans (prog g) (ProgPost i) i
  progPostWP g (e , s) = {!!}

  -- ({!!} represents the hole where the proof will be developed)

  -- In the following, each time we take a step, the goal in each hole is much more manageable and
  -- understandable than the unwieldy one shown above for the direct approach.

  -- C-c C-c in the *empty* hole, press enter to split on result

  progPostWP g (e , s) r x = {!!}

  -- r and x are introduced by the bindPT field of RWSPT; r is a return value from the gets call in
  -- inner, and x is evidence that r is the result of applying function g to the state (second
  -- component of the input for RWS), so now our goal is reduced to proving that the predicate
  -- transformer for the continuation with respect to RWSbindPost holds (note that gets produces no
  -- outputs).

  -- C-c C-c in the *empty* hole again, press enter to split on result

  proj₁ (progPostWP g (e , s) r x) = {!!}
  proj₂ (progPostWP g (e , s) r x) = {!!}

  -- Optionally, the proof engineer can replace the names generated automatically by Agda
  -- with more meaningful ones.  By changing r to m, we maintain the correspondence to the
  -- program variable, and by changing x to mId, we reflect the intuition that m is an
  -- alias for g s.

  proj₁ (progPostWP g (e , s) m mId) = {!!}
  proj₂ (progPostWP g (e , s) m mId) = {!!}

  -- Because the continuation is a maybeAST, the proof goal is determined by opPT ... (Right
  -- (BCmaybe mb)) ... in Dijkstra.AST.Branching.PredTransExtension.  Therefore, we have two
  -- obligations, one for the case in which the value returned by gets (which x tells us is the same
  -- as r) is a just, and one for when it is nothing.

  -- Using C-c C-c to split on result in *each* hole

  proj₁ (progPostWP g (e , s) m mId) j x r₁ x₁ o' x₂ = {!!}
  proj₂ (progPostWP g (e , s) m mId)   x       o' x₁ = {!!}

  -- For the just case, Agda has introduced j : Wr and evidence x that m is just j, as determined
  -- by the first conjunct of opPT ... (Right (BCmaybe mb)).  Similarly, for the nothing case,
  -- Agda has introduced evidence x that r is nothing.

  -- For each case, Agda has further unrolled the respective proof obligations.  In the just case,
  -- we have another bind (tell and then return), so Agda unrolls our proof obligations using bindPT
  -- RWSPT again, providing a return value r₁ for the tell (which is simply Unit, as tell does not
  -- return anything interesting) and evidence x₁ that it is the value returned by the tell, which
  -- is unit.

  -- Finally, prog g calls pass (syntactic sugar for the RWSpass command) with the result of the
  -- continuation.  Therefore the respective proof goals are further expanded (via opPT ... RWSpass and
  -- RWSpassPost), introducing a variable o' : List Wr and evidence (x₂ in the just case, x₁ in the
  -- nothing case) that o' is the result of running the respective branches.  In each case, o' is
  -- equivalent to [].  In the just case, this is because pass receives a function that deletes all
  -- the outputs produced, and in the nothing case, no outputs have been produced, so
  -- doubling the list of outputs still results in an empty list.  Thus, we have x₂ : o' ≡ ([] ++
  -- []) ++ [] ++ [] in the just case and x₁ : o' ≡ [] for the nothing case.

  -- Next, we use C-c C-c again, this time providing x₂ in the just case and x₁ in the nothing case.

  proj₁ (progPostWP2 g (e , s) m mId) j x r x₁ .[] refl = {!!}
  proj₂ (progPostWP2 g (e , s) m mId)   x      .[] refl = {!!}

  -- Agda has figured out that the output lists are [] in each case.

  -- C-c C-r in each hole splits each goal into a product for the two conjuncts of ProgPost i

  proj₁ (progPostWP2 g (e , s) m mId) j x r x₁ .[] refl = {!!} , {!!}
  proj₂ (progPostWP2 g (e , s) m mId)   x      .[] refl = {!!} , {!!}

  -- C-c C-r in each hole completes the proof because Agda has sufficient information (that the
  -- state is unchanged for the first conjunct and that the length of the list of Wrs produced
  -- is zero) to easily discharge the proof obligations.

  proj₁ (progPostWP2 g (e , s) m mId) j x r x₁ .[] refl = refl , refl
  proj₂ (progPostWP2 g (e , s) m mId)   x      .[] refl = refl , refl

  -- The final proof:

  proj₂ (progPostWP _ _ _ _) _ _ _ _ _ refl = refl , refl
  proj₂ (progPostWP _ _ _ _) _       _ refl = refl , refl

  -- is the same, but hides variables that don't need to be exposed.  We don't need to name or
  -- pattern match on anything other than the evidence that the list of outputs produced is
  -- equivalent to the empty list, enabling proof that its length is zero, as required by the second
  -- conjunct of the postcondition.

-}

-- As we have proved that the precondition determined by predTrans (prog f) (ProgPost i) holds for
-- all i, we can use sufficiency to prove that the postcondition holds after running the program
-- for any input
progPost' : ∀ g i → ProgPost i (runRWSAST (prog g) i)
progPost' g i = sufficient (prog g) (ProgPost i) i (progPostWP g i)
