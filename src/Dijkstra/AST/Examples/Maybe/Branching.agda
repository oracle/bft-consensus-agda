{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Data.Nat
import      Level
open import Util.Prelude hiding (bail)
open import Dijkstra.AST.Maybe

module Dijkstra.AST.Examples.Maybe.Branching where

module Example-if (n : ℕ) where
  -- First we specify the behaviour we want via a postcondition requiring that the program can fail
  -- only if n is zero, and if it succeeds, the n is non-zero and the result is 2 * n
  bpPost : Post ℕ
  bpPost nothing   = n ≡ 0
  bpPost (just n') = 0 < n × n' ≡ 2 * n

  module Raw where
    -- A program that includes branching in MaybeAST, intended to satify the specification
    -- established by bpPost

    -- Because this is a "raw" example that does not use the nice syntax, we have to explicitly
    -- import and open modules to access the underlying definitions
    open import Dijkstra.AST.Branching using (BranchCmd)
    open BranchCmd using (BCif)
    open MaybeBase using (Maybe-bail)

    branchingProg : MaybeAST ℕ
    branchingProg = ASTop (Right (BCif (toBool (n ≟ℕ 0) )))
                          (λ { (lift false) → ASTreturn (2 * n)
                             ; (lift true)  → ASTop (Left Maybe-bail) λ () })

    -- The weakest precondition for bpPost holds
    branchingProgWP : (i : Input)
                      → predTrans branchingProg bpPost i

    {- TUTORIAL: A simple proof using the branching support for AST MaybeExtOps, specifically BCif.

    If we start with

      branchingProgWP i = ?

    As seen after C-c C-l, or by doing C-u C-c C- in the hole, the goal is of type:

      ASTPredTrans.predTrans MaybePTExt branchingProg bpPost i

    Using C-c C-, (without the C-u prefix), tells us a bit more
    detail about the goal:

      ASTPredTrans.opPT MaybePTExt (Right (BCif ⌊ n ≟ℕ 0 ⌋))
        (λ x →
           ASTPredTrans.predTrans MaybePTExt
           ((λ { (lift false) → ASTreturn (2 * n)
               ; (lift true) → ASTop (Left Maybe-bail) (λ ())
               })
            x))
        bpPost i

    This is because branchingProg starts with an ASTop (see ASTPredTrans.predTrans (ASTop c f)).
    It's still not very easy to see what needs to be proved.  Doing C-u C-u C-c C-, in the hole goes
    further, revealing the following:

      Σ
        (isYes
         (map′ (≡ᵇ⇒≡ n 0) (≡⇒≡ᵇ n 0) (Data.Bool.Properties.T? (n ≡ᵇ 0)))
         ≡ true →
         n ≡ 0)
        (λ x →
           isYes
           (map′ (≡ᵇ⇒≡ n 0) (≡⇒≡ᵇ n 0) (Data.Bool.Properties.T? (n ≡ᵇ 0)))
           ≡ false →
           Σ (1 ≤ n) (λ x₁ → n + (n + 0) ≡ n + (n + 0)))

    We can see that this is a product, and that each conjunct receives evidence that the condition
    evaluates to the relevant boolean value (true for the first, false for the second).  This is
    because

      ASTPredTrans.opPT BranchPT (Right (BCif c)) f P i

    requires two proofs, one for when the condition c is true and one for when it's false; each case
    gets evidence that the condition evaluates to the relevant boolean.

    Furthermore, we can see that the goals for each conjunct are now derived from the postcondition,
    bpPost.  Now we can start to see what we need to prove.

    The second conjunct does not depend on the first, so we can separate into two goals:

      proj₁ (branchingProgWP _) = ?
      proj₂ (branchingProgWP _) = ?

    Using C-c C-, in the first hole gives us this goal:

      ⌊ n ≟ℕ 0 ⌋ ≡ true → n ≡ 0

    This can be dispatched with toWitnessT:

      proj₁ (branchingProgWP _) = toWitnessT

    Equivalently, let's give the evidence that ⌊ n ≟ℕ 0 ⌋ ≡ true a name for consistency with the
    false case below:

      proj₁ (branchingProgWP _) isTrue = toWitnessT isTrue

    The second conjunct is similar.  Doing C-c C-, in the hole shows:

      ⌊ n ≟ℕ 0 ⌋ ≡ false → 0 < n × n + (n + zero) ≡ n + (n + zero)

    Let's give the evidence that the condition is false a name, so we can
    prove the two conjuncts separately:

      proj₂ (branchingProgWP _) isFalse = ?

    The goal shown by C-c C-, is now:

      0 < n × n + (n + zero) ≡ n + (n + zero)

    We can do C-c C-r to refine this to two separate goals, the first of which is 0 < n.  Again, we
    use the relevant toWitness function (toWitnessF because the condition is false), along with a
    library function n≢0⇒n>0 to fill the hole for the first conjunct.

      proj₂ (branchingProgWP _) isFalse = (n≢0⇒n>0 (toWitnessF isFalse)) , ?

    C-c C-, shows that the second hole needs evidence that n + (n + zero) ≡ n + (n + zero), which is
    easily satisfied by refl, resulting in the complete proof below.

    One important lesson is to remember to use the variants of C-c C-, with zero, one or two C-u's
    before it.  Each is the most useful of the three in some contexts.  Experienced users might
    predict which one is best, but just having enough experience to remember to try all three is a
    big help.

    -}

    proj₁ (branchingProgWP _) isTrue  =           toWitnessT isTrue
    proj₂ (branchingProgWP _) isFalse = (n≢0⇒n>0 (toWitnessF isFalse)) , refl

    -- And therefore, the result of running the program satisfies the postcondition
    prop : (i : Input) → bpPost (runMaybeAST branchingProg i)
    prop i =
      sufficient branchingProg bpPost i (branchingProgWP i)

  module Prettier where
    -- Same program with nicer syntax using ifAST, bail and return
    branchingProg : MaybeAST ℕ
    branchingProg = ifAST ⌊ n ≟ℕ 0 ⌋
                    then bail
                    else (return (2 * n))

    --  Note that the same proof works for both versions (as they are equivalent)
    branchingProgWP : (i : Input)
                         → predTrans branchingProg bpPost i
    proj₁ (branchingProgWP _) isTrue  =           toWitnessT isTrue
    proj₂ (branchingProgWP _) isFalse = (n≢0⇒n>0 (toWitnessF isFalse)) , refl

    prop : (i : Input) → bpPost (runMaybeAST branchingProg i)
    prop i = sufficient branchingProg bpPost i (branchingProgWP i)

module Example-either (n : ℕ) where

  module Common where

    _monus1 : ℕ → Either Unit ℕ
    _monus1 0        = Left unit
    _monus1 (suc n') = Right n'

    monus1lemma1 : ∀ {n'} → n ≡ n' → ∀ {l} → n' monus1 ≡ Left l → n ≡ 0
    monus1lemma1 {n'} n≡n' _
       with n'
    ...| 0 = n≡n'

    monus1lemma2 : ∀ {nalias} → n ≡ nalias → ∀ {n'} → nalias monus1 ≡ Right n' → n ≡ suc n'
    monus1lemma2 {nalias} n≡nalias isrgt
       with nalias
    ...| suc x rewrite n≡nalias | inj₂-injective isrgt = refl

    bpPost : Post ℕ
    bpPost nothing  = n ≡ 0
    bpPost (just x) = n ≡ suc x

  module Raw where
    open Common
    -- Because this is a "raw" example that does not use the nice syntax, we have to explicitly
    -- import and open modules to access the underlying definitions
    open import Dijkstra.AST.Branching using (BranchCmd)
    open BranchCmd using (BCif ; BCeither)
    open MaybeBase using (Maybe-bail)

    -- A branching program that bails if n monus1 is Left _
    -- and returns b if n monus1 is Right b
    branchingProg : MaybeAST ℕ
    branchingProg = ASTop (Right (BCeither (n monus1)))
                          λ { (lift (Left  a)) → ASTop (Left Maybe-bail) λ () 
                            ; (lift (Right b)) → return b
                            }

    branchingProgWP : (i : Input)
                      → predTrans branchingProg bpPost i
    proj₁ (branchingProgWP _) l islft = monus1lemma1 refl islft
    proj₂ (branchingProgWP _) l isrgt = monus1lemma2 refl isrgt

    prop : (i : Input) → bpPost (runMaybeAST branchingProg i)
    prop i = sufficient branchingProg bpPost i (branchingProgWP i)

  module Prettier where
    open Common
    -- Same program with nicer syntax using eitherSAST, bail and return
    branchingProg : MaybeAST ℕ
    branchingProg = eitherSAST (n monus1) (const bail) return

    branchingProgWP : (i : Input)
                      → predTrans branchingProg bpPost i
    proj₁ (branchingProgWP _) l islft = monus1lemma1 refl islft
    proj₂ (branchingProgWP _) l isrgt = monus1lemma2 refl isrgt

    prop : (i : Input) → bpPost (runMaybeAST branchingProg i)
    prop i = sufficient branchingProg bpPost i (branchingProgWP i)
