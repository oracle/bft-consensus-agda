{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Prelude

-- This module defines functionality modeling an RWST monad, which we use to
-- define an implementation, and functionality for proving properties about
-- programs written using this RWST monad. The main definitions are:
-- 1. RWST, a datatype for the ASTs of stateful programs that read from an
--    environment and produce output.
--    This datatype includes constructors for branching code, to aid in the
--    verification effort (see below).
-- 2. RWST-weakestPre, a large elimination that, given an RWST program and a
--    post condition for the program, produces the weakest precondition needed
--    to satisfy that post condition. Branches in code using the constructors
--    `RWST-if` and friends are translated into products, with each component of
--    the product corresponding to a possible branch taken.
-- 3. RWST-Contract is the type of proofs that, given a stateful computation and
--    a post condition, the weakest precondition suffices to prove that post
--    condition.
-- 4. RWST-contract proves RWST-Contract, i.e., for every stateful computation
--    `m` and post condition `P`, given a proof over a pre-state `pre` the
--    weakest precondition for `P` holds, then postcondition `P` holds for the
--    post-state obtained from running `m` in state `pre`.

-- TODO-2: this module is independent of any particular implementation
-- and arguably belongs somewhere more general, such as next to Optics.

module LibraBFT.ImplShared.Util.Dijkstra.RWST where

-- RWST, the AST of computations with state `St` reading from an environment
-- `Ev` and producing a list of outputs of type `Wr`
data RWST (Ev Wr St : Set) : Set → Set₁ where
  -- Primitive combinators
  RWST-return : ∀ {A}   → A                                       → RWST Ev Wr St A
  RWST-bind   : ∀ {A B} → RWST Ev Wr St A → (A → RWST Ev Wr St B) → RWST Ev Wr St B
  RWST-gets   : ∀ {A} → (St → A)                                  → RWST Ev Wr St A
  RWST-put    : St                                                → RWST Ev Wr St Unit
  RWST-ask    :                                                     RWST Ev Wr St Ev
  RWST-tell   : List Wr                                           → RWST Ev Wr St Unit
  -- Branching combinators (used for creating more convenient contracts)
  RWST-if     : ∀ {A} → Guards (RWST Ev Wr St A)                  → RWST Ev Wr St A
  RWST-either : ∀ {A B C} → Either B C
                → (B → RWST Ev Wr St A) → (C → RWST Ev Wr St A)   → RWST Ev Wr St A
  RWST-ebind  : ∀ {A B C}
                → RWST Ev Wr St (Either C A)
                → (A → RWST Ev Wr St (Either C B))                → RWST Ev Wr St (Either C B)
  RWST-maybe  : ∀ {A B} → Maybe B
                → (RWST Ev Wr St A) → (B → RWST Ev Wr St A)       → RWST Ev Wr St A

private
  variable
    Ev Wr St : Set
    A B C    : Set

-- To execute an RWST program, you provide an environment and prestate. This
-- produces a result value, poststate, and list of outputs.
RWST-run : RWST Ev Wr St A → Ev → St → A × St × List Wr
RWST-run (RWST-return x) ev st  = x , st , []
RWST-run (RWST-bind m f) ev st
   with RWST-run m ev st
...| x₁ , st₁ , outs₁
   with RWST-run (f x₁) ev st₁
...| x₂ , st₂ , outs₂           = x₂ , st₂ , outs₁ ++ outs₂
RWST-run (RWST-gets f) ev st    = f st , st , []
RWST-run (RWST-put st) ev _     = unit , st , []
RWST-run RWST-ask ev st         = ev , st , []
RWST-run (RWST-tell outs) ev st = unit , st , outs
RWST-run (RWST-if (clause (b ≔ c) gs)) ev st =
  if toBool b then RWST-run c ev st else RWST-run (RWST-if gs) ev st
RWST-run (RWST-if (otherwise≔ c)) ev st = RWST-run c ev st
RWST-run (RWST-either (Left x) f₁ f₂) ev st = RWST-run (f₁ x) ev st
RWST-run (RWST-either (Right y) f₁ f₂) ev st = RWST-run (f₂ y) ev st
RWST-run (RWST-ebind m f) ev st
   with RWST-run m ev st
...| Left c , st₁ , outs₁ = Left c , st₁ , outs₁
...| Right a , st₁ , outs₁
   with RWST-run (f a) ev st₁
...| r , st₂ , outs₂ = r , st₂ , outs₁ ++ outs₂
RWST-run (RWST-maybe nothing f₁ f₂) ev st = RWST-run f₁ ev st
RWST-run (RWST-maybe (just x) f₁ f₂) ev st = RWST-run (f₂ x) ev st

-- Accessors for the result, poststate, and outputs.
RWST-result : RWST Ev Wr St A → Ev → St → A
RWST-result m ev st = proj₁ (RWST-run m ev st)

RWST-post : RWST Ev Wr St A → Ev → St → St
RWST-post m ev st = proj₁ (proj₂ (RWST-run m ev st))

RWST-outs : RWST Ev Wr St A → Ev → St → List Wr
RWST-outs m ev st = proj₂ (proj₂ (RWST-run m ev st))

-- Preconditions are predicates over environments and prestates.
RWST-Pre : (Ev St : Set) → Set₁
RWST-Pre Ev St = (ev : Ev) (pre : St) → Set

-- Postconditions are predicates over a result, poststate, and list of outputs.
RWST-Post : (Wr St A : Set) → Set₁
RWST-Post Wr St A = (x : A) (post : St) (outs : List Wr) → Set

RWST-Post-⇒ : (P Q : RWST-Post Wr St A) → Set
RWST-Post-⇒ P Q = ∀ r st outs → P r st outs → Q r st outs

-- RWST-weakestPre computes a predicate transformer: it maps a RWST
-- computation `m` and desired postcondition `Post` to the weakest precondition
-- needed to prove `P` holds after running `m`.
RWST-PredTrans : (Ev Wr St A : Set) → Set₁
RWST-PredTrans Ev Wr St A = RWST-Post Wr St A → RWST-Pre Ev St

-- When RWST computations are sequenced, e.g., `RWST-bind m λ x → f x`,
-- outputs are concatenated. The postcondition desired for the above sequence
-- becomes a postcondition for `f x` in which the outputs of `m` are prepended
-- to the outputs of `f x`.
RWST-Post++ : ∀ {Wr St A} → RWST-Post Wr St A → List Wr → RWST-Post Wr St A
RWST-Post++ P outs x post outs₁ = P x post (outs ++ outs₁)

-- Consider again the sequence `RWST-bind m₁ λ x → f x`. We also translate a
-- postcondition `P` for the sequence into a postcondition for `m` ---
-- specifically, the post condition we want for `m` is that the weakest
-- precondition for `RWST-Post++ P outs` holds, where `outs` are the outputs of
-- `m`.
RWST-weakestPre-bindPost  : (ev : Ev) (f : A → RWST Ev Wr St B) → RWST-Post Wr St B → RWST-Post Wr St A
RWST-weakestPre-ebindPost : (ev : Ev) (f : A → RWST Ev Wr St (C ⊎ B)) → RWST-Post Wr St (C ⊎ B) → RWST-Post Wr St (C ⊎ A)

RWST-weakestPre : (m : RWST Ev Wr St A) → RWST-PredTrans Ev Wr St A
RWST-weakestPre (RWST-return x) P ev pre = P x pre []
RWST-weakestPre (RWST-bind m f) P ev pre =
  RWST-weakestPre m (RWST-weakestPre-bindPost ev f P) ev pre
RWST-weakestPre (RWST-gets f) P ev pre = P (f pre) pre []
RWST-weakestPre (RWST-put post) P ev pre = P unit post []
RWST-weakestPre RWST-ask P ev pre = P ev pre []
RWST-weakestPre (RWST-tell outs) P ev pre = P unit pre outs
RWST-weakestPre (RWST-if (clause (b ≔ c) gs)) P ev pre =
  (toBool b ≡ true → RWST-weakestPre c P ev pre)
  × (toBool b ≡ false → RWST-weakestPre (RWST-if gs) P ev pre)
RWST-weakestPre (RWST-if (otherwise≔ c)) P ev pre =
  RWST-weakestPre c P ev pre
RWST-weakestPre (RWST-either e f₁ f₂) P ev pre =
    (∀ x → (e ≡ Left x) →
      RWST-weakestPre (f₁ x) P ev pre)
  × (∀ y → (e ≡ Right y) →
       RWST-weakestPre (f₂ y) P ev pre)
RWST-weakestPre (RWST-ebind m f) P ev pre =
  RWST-weakestPre m (RWST-weakestPre-ebindPost ev f P) ev pre
RWST-weakestPre (RWST-maybe m f₁ f₂) P ev pre =
  (m ≡ nothing → RWST-weakestPre f₁ P ev pre)
  × (∀ j → m ≡ just j → RWST-weakestPre (f₂ j) P ev pre)

RWST-weakestPre-ebindPost ev f Post (Left r) post outs =
  Post (Left r) post outs
RWST-weakestPre-ebindPost ev f Post (Right r) post outs =
  ∀ c → c ≡ r → RWST-weakestPre (f c) (RWST-Post++ Post outs) ev post

RWST-weakestPre-bindPost ev f Post x post outs =
  ∀ r → r ≡ x → RWST-weakestPre (f r) (RWST-Post++ Post outs) ev post

-- The post condition `P` holds for `m` with environment `ev` and prestate `pre`
RWST-Post-True : (P : RWST-Post Wr St A) (m : RWST Ev Wr St A) (ev : Ev) (pre : St) → Set
RWST-Post-True P m ev pre =
  let (x , post , outs) = RWST-run m ev pre in
  P x post outs

-- For every RWST computation `m`, `RWST-Contract m` is the type of proofs that,
-- for all post conditions `P`, starting environments `ev` and prestates `pre`,
-- to prove that `P` holds after running `m` in `ev` and `pre`, it suffices to
-- provide a proof of the weakest precondition for `P` with respect to `m`,
-- `ev`, and `pre`.
RWST-Contract : (m : RWST Ev Wr St A) → Set₁
RWST-Contract{Ev}{Wr}{St}{A} m =
  (P : RWST-Post Wr St A)
  → (ev : Ev) (pre : St) → RWST-weakestPre m P ev pre
  → RWST-Post-True P m ev pre

-- This proves that `RWST-weakestPre` gives a *sufficient* precondition for
-- establishing a desired postcondition. Note thought that it does not prove
-- that this precondition is the weakest such one; even though this is true, it
-- is not important for our purposes.
RWST-contract : (m : RWST Ev Wr St A) → RWST-Contract m
RWST-contract (RWST-return x₁) P ev pre wp = wp
RWST-contract (RWST-bind m f) P ev pre wp
   with RWST-contract m _ ev pre wp
...| con
   with RWST-run m ev pre
...| x₁ , st₁ , outs₁ =
  RWST-contract (f x₁) _ ev st₁ (con x₁ refl)
RWST-contract (RWST-gets f) P ev pre wp = wp
RWST-contract (RWST-put x₁) P ev pre wp = wp
RWST-contract RWST-ask P ev pre wp = wp
RWST-contract (RWST-tell x₁) P ev pre wp = wp
RWST-contract{Ev}{Wr}{St}{A} (RWST-if gs) P ev pre wp = RWST-contract-if gs P ev pre wp
  where
  RWST-contract-if : (gs : Guards (RWST Ev Wr St A)) → RWST-Contract (RWST-if gs)
  RWST-contract-if (clause (b ≔ c) gs) P ev pre (wp₁ , wp₂)
    with toBool b
  ...| true = RWST-contract c _ ev pre (wp₁ refl)
  ...| false = RWST-contract-if gs _ ev pre (wp₂ refl)
  RWST-contract-if (otherwise≔ x) P ev pre wp =
    RWST-contract x P ev pre wp
RWST-contract (RWST-either (Left x) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWST-contract (f₁ x) _ ev pre (wp₁ x refl)
RWST-contract (RWST-either (Right y) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWST-contract (f₂ y) _ ev pre (wp₂ y refl)
RWST-contract (RWST-ebind m f) P ev pre wp
   with RWST-contract m _ ev pre wp
...| con
   with RWST-run m ev pre
... | Left x , st₁ , outs₁ = con
... | Right y , st₁ , outs₁ = RWST-contract (f y) _ ev st₁ (con y refl)
RWST-contract (RWST-maybe nothing f₁ f₂) P ev pre (wp₁ , wp₂)
  = RWST-contract f₁ _ ev pre (wp₁ refl)
RWST-contract (RWST-maybe (just x) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWST-contract (f₂ x) _ ev pre (wp₂ x refl)

-- This helper function is primarily used to take a proof concerning one
-- computation `m` and show that that proof implies a property concerning a
-- larger computation which contains `m`.
RWST-⇒
  : (P Q : RWST-Post Wr St A) → (RWST-Post-⇒ P Q)
    → ∀ m (ev : Ev) st → RWST-weakestPre m P ev st → RWST-weakestPre m Q ev st
RWST-⇒ P Q pf (RWST-return x) ev st pre = pf x st [] pre
RWST-⇒ P Q pf (RWST-bind m f) ev st pre =
  RWST-⇒ _ _
    (λ r₁ st₁ outs₁ pf₁ x x≡ →
      RWST-⇒ _ _
        (λ r₂ st₂ outs₂ pf₂ → pf r₂ st₂ (outs₁ ++ outs₂) pf₂)
        (f x) ev st₁ (pf₁ x x≡))
    m ev st pre
RWST-⇒ P Q pf (RWST-gets f) ev st pre = pf _ _ _ pre
RWST-⇒ P Q pf (RWST-put x) ev st pre = pf _ _ _ pre
RWST-⇒ P Q pf RWST-ask ev st pre = pf _ _ _ pre
RWST-⇒ P Q pf (RWST-tell x) ev st pre = pf _ _ _ pre
RWST-⇒ P Q pf (RWST-if (otherwise≔ x)) ev st pre = RWST-⇒ _ _ pf x ev st pre
RWST-⇒ P Q pf (RWST-if (clause (b ≔ c) cs)) ev st (pre₁ , pre₂) =
  (λ pf' → RWST-⇒ _ _ pf c ev st (pre₁ pf'))
  , λ pf' → RWST-⇒ _ _ pf (RWST-if cs) ev st (pre₂ pf')
proj₁ (RWST-⇒ P Q pf (RWST-either (Left x) f₁ f₂) ev st (pre₁ , pre₂)) x₁ x₁≡ =
  RWST-⇒ _ _ pf (f₁ x₁) ev st (pre₁ x₁ x₁≡)
proj₂ (RWST-⇒ P Q pf (RWST-either (Left x) f₁ f₂) ev st (pre₁ , pre₂)) y ()
proj₁ (RWST-⇒ P Q pf (RWST-either (Right y) f₁ f₂) ev st (pre₁ , pre₂)) y₁ ()
proj₂ (RWST-⇒ P Q pf (RWST-either (Right y) f₁ f₂) ev st (pre₁ , pre₂)) y₁ y₁≡ =
  RWST-⇒ _ _ pf (f₂ y₁) ev st (pre₂ y₁ y₁≡)
RWST-⇒ P Q pf (RWST-ebind m f) ev st pre =
  RWST-⇒ _ _
    (λ { (Left x₁) st₁ outs x → pf _ _ _ x
       ; (Right y) st₁ outs x → λ c x₁ →
           RWST-⇒ _ _ (λ r st₂ outs₁ x₂ → pf r st₂ (outs ++ outs₁) x₂) (f c) ev st₁ (x c x₁)})
    m ev st pre
proj₁ (RWST-⇒ P Q pf (RWST-maybe x m f) ev st (pre₁ , pre₂)) ≡nothing = RWST-⇒ _ _ pf m ev st (pre₁ ≡nothing)
proj₂ (RWST-⇒ P Q pf (RWST-maybe x m f) ev st (pre₁ , pre₂)) b b≡ = RWST-⇒ _ _ pf (f b) ev st (pre₂ b b≡)

RWST-⇒-bind
  : (P : RWST-Post Wr St A) (Q : RWST-Post Wr St B)
    → (f : A → RWST Ev Wr St B) (ev : Ev)
    → RWST-Post-⇒ P (RWST-weakestPre-bindPost ev f Q)
    → ∀ m st → RWST-weakestPre m P ev st
    → RWST-weakestPre (RWST-bind m f) Q ev st
RWST-⇒-bind P Q f ev pf m st con =
  RWST-⇒ P ((RWST-weakestPre-bindPost ev f Q)) pf m ev st con

RWST-⇒-ebind
  : (P : RWST-Post Wr St (Either C A)) (Q : RWST-Post Wr St (Either C B))
    → (f : A → RWST Ev Wr St (Either C B)) (ev : Ev)
    → RWST-Post-⇒ P (RWST-weakestPre-ebindPost ev f Q)
    → ∀ m st → RWST-weakestPre m P ev st
    → RWST-weakestPre (RWST-ebind m f) Q ev st
RWST-⇒-ebind P Q f ev pf m st con =
  RWST-⇒ P ((RWST-weakestPre-ebindPost ev f Q)) pf m ev st con
