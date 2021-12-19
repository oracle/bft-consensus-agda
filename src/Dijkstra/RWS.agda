{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module provides functionality for proving properties about
-- programs written using this RWS monad. The main definitions are:
-- -  RWS-weakestPre, a large elimination that, given an RWS program and a
--    post condition for the program, produces the weakest precondition needed
--    to satisfy that post condition. Branches in code using the constructors
--    `RWS-if` and friends are translated into products, with each component of
--    the product corresponding to a possible branch taken.
-- -  RWS-Contract is the type of proofs that, given a stateful computation and
--    a post condition, the weakest precondition suffices to prove that post
--    condition.
-- -  RWS-contract proves RWS-Contract, i.e., for every stateful computation
--    `m` and post condition `P`, given a proof over a pre-state `pre` the
--    weakest precondition for `P` holds, then postcondition `P` holds for the
--    post-state obtained from running `m` in state `pre`.

module Dijkstra.RWS where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Haskell.Modules.RWS
open import Haskell.Prelude

private
  variable
    Ev Wr St : Set
    A B C    : Set

-- Preconditions are predicates over environments and prestates.
RWS-Pre : (Ev St : Set) → Set₁
RWS-Pre Ev St = (ev : Ev) (pre : St) → Set

-- Postconditions are predicates over a result, poststate, and list of outputs.
RWS-Post : (Wr St A : Set) → Set₁
RWS-Post Wr St A = (x : A) (post : St) (outs : List Wr) → Set

RWS-Post-⇒ : (P Q : RWS-Post Wr St A) → Set
RWS-Post-⇒ P Q = ∀ r st outs → P r st outs → Q r st outs

-- RWS-weakestPre computes a predicate transformer: it maps a RWS
-- computation `m` and desired postcondition `Post` to the weakest precondition
-- needed to prove `P` holds after running `m`.
RWS-PredTrans : (Ev Wr St A : Set) → Set₁
RWS-PredTrans Ev Wr St A = RWS-Post Wr St A → RWS-Pre Ev St

-- When RWS computations are sequenced, e.g., `RWS-bind m λ x → f x`,
-- outputs are concatenated. The postcondition desired for the above sequence
-- becomes a postcondition for `f x` in which the outputs of `m` are prepended
-- to the outputs of `f x`.
RWS-Post++ : ∀ {Wr St A} → RWS-Post Wr St A → List Wr → RWS-Post Wr St A
RWS-Post++ P outs x post outs₁ = P x post (outs ++ outs₁)

-- Consider again the sequence `RWS-bind m₁ λ x → f x`. We also translate a
-- postcondition `P` for the sequence into a postcondition for `m` ---
-- specifically, the post condition we want for `m` is that the weakest
-- precondition for `RWS-Post++ P outs` holds, where `outs` are the outputs of
-- `m`.
RWS-weakestPre-bindPost  : (ev : Ev) (f : A → RWS Ev Wr St B) → RWS-Post Wr St B → RWS-Post Wr St A
RWS-weakestPre-ebindPost : (ev : Ev) (f : A → RWS Ev Wr St (Either C B)) → RWS-Post Wr St (Either C B) → RWS-Post Wr St (Either C A)

RWS-weakestPre : (m : RWS Ev Wr St A) → RWS-PredTrans Ev Wr St A
RWS-weakestPre (RWS-return x) P ev pre = P x pre []
RWS-weakestPre (RWS-bind m f) P ev pre =
  RWS-weakestPre m (RWS-weakestPre-bindPost ev f P) ev pre
RWS-weakestPre (RWS-gets f) P ev pre = P (f pre) pre []
RWS-weakestPre (RWS-put post) P ev pre = P unit post []
RWS-weakestPre RWS-ask P ev pre = P ev pre []
RWS-weakestPre (RWS-tell outs) P ev pre = P unit pre outs
RWS-weakestPre (RWS-if (clause (b ≔ c) gs)) P ev pre =
  (toBool b ≡ true → RWS-weakestPre c P ev pre)
  × (toBool b ≡ false → RWS-weakestPre (RWS-if gs) P ev pre)
RWS-weakestPre (RWS-if (otherwise≔ c)) P ev pre =
  RWS-weakestPre c P ev pre
RWS-weakestPre (RWS-either e f₁ f₂) P ev pre =
    (∀ x → (e ≡ Left x) →
      RWS-weakestPre (f₁ x) P ev pre)
  × (∀ y → (e ≡ Right y) →
       RWS-weakestPre (f₂ y) P ev pre)
RWS-weakestPre (RWS-ebind m f) P ev pre =
  RWS-weakestPre m (RWS-weakestPre-ebindPost ev f P) ev pre
RWS-weakestPre (RWS-maybe m f₁ f₂) P ev pre =
  (m ≡ nothing → RWS-weakestPre f₁ P ev pre)
  × (∀ j → m ≡ just j → RWS-weakestPre (f₂ j) P ev pre)

RWS-weakestPre-ebindPost ev f Post (Left r) post outs =
  Post (Left r) post outs
RWS-weakestPre-ebindPost ev f Post (Right r) post outs =
  ∀ c → c ≡ r → RWS-weakestPre (f c) (RWS-Post++ Post outs) ev post

RWS-weakestPre-bindPost ev f Post x post outs =
  ∀ r → r ≡ x → RWS-weakestPre (f r) (RWS-Post++ Post outs) ev post

-- The post condition `P` holds for `m` with environment `ev` and prestate `pre`
RWS-Post-True : (P : RWS-Post Wr St A) (m : RWS Ev Wr St A) (ev : Ev) (pre : St) → Set
RWS-Post-True P m ev pre =
  let (x , post , outs) = runRWS m ev pre in
  P x post outs

-- For every RWS computation `m`, `RWS-Contract m` is the type of proofs that,
-- for all post conditions `P`, starting environments `ev` and prestates `pre`,
-- to prove that `P` holds after running `m` in `ev` and `pre`, it suffices to
-- provide a proof of the weakest precondition for `P` with respect to `m`,
-- `ev`, and `pre`.
RWS-Contract : (m : RWS Ev Wr St A) → Set₁
RWS-Contract{Ev}{Wr}{St}{A} m =
  (P : RWS-Post Wr St A)
  → (ev : Ev) (pre : St) → RWS-weakestPre m P ev pre
  → RWS-Post-True P m ev pre

-- This proves that `RWS-weakestPre` gives a *sufficient* precondition for
-- establishing a desired postcondition. Note thought that it does not prove
-- that this precondition is the weakest such one; even though this is true, it
-- is not important for our purposes.
RWS-contract : (m : RWS Ev Wr St A) → RWS-Contract m
RWS-contract (RWS-return x₁) P ev pre wp = wp
RWS-contract (RWS-bind m f) P ev pre wp
   with RWS-contract m _ ev pre wp
...| con
   with runRWS m ev pre
...| x₁ , st₁ , outs₁ =
  RWS-contract (f x₁) _ ev st₁ (con x₁ refl)
RWS-contract (RWS-gets f) P ev pre wp = wp
RWS-contract (RWS-put x₁) P ev pre wp = wp
RWS-contract RWS-ask P ev pre wp = wp
RWS-contract (RWS-tell x₁) P ev pre wp = wp
RWS-contract{Ev}{Wr}{St}{A} (RWS-if gs) P ev pre wp = RWS-contract-if gs P ev pre wp
  where
  RWS-contract-if : (gs : Guards (RWS Ev Wr St A)) → RWS-Contract (RWS-if gs)
  RWS-contract-if (clause (b ≔ c) gs) P ev pre (wp₁ , wp₂)
    with toBool b
  ...| true = RWS-contract c _ ev pre (wp₁ refl)
  ...| false = RWS-contract-if gs _ ev pre (wp₂ refl)
  RWS-contract-if (otherwise≔ x) P ev pre wp =
    RWS-contract x P ev pre wp
RWS-contract (RWS-either (Left x) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWS-contract (f₁ x) _ ev pre (wp₁ x refl)
RWS-contract (RWS-either (Right y) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWS-contract (f₂ y) _ ev pre (wp₂ y refl)
RWS-contract (RWS-ebind m f) P ev pre wp
   with RWS-contract m _ ev pre wp
...| con
   with runRWS m ev pre
... | Left x , st₁ , outs₁ = con
... | Right y , st₁ , outs₁ = RWS-contract (f y) _ ev st₁ (con y refl)
RWS-contract (RWS-maybe nothing f₁ f₂) P ev pre (wp₁ , wp₂)
  = RWS-contract f₁ _ ev pre (wp₁ refl)
RWS-contract (RWS-maybe (just x) f₁ f₂) P ev pre (wp₁ , wp₂) =
  RWS-contract (f₂ x) _ ev pre (wp₂ x refl)

-- This helper function is primarily used to take a proof concerning one
-- computation `m` and show that that proof implies a property concerning a
-- larger computation which contains `m`.
RWS-⇒
  : ∀ {P Q : RWS-Post Wr St A}
    → ∀ m (ev : Ev) st
    → RWS-weakestPre m P ev st
    → RWS-Post-⇒ P Q
    → RWS-weakestPre m Q ev st
RWS-⇒ (RWS-return x) ev st pre pf = pf x st [] pre
RWS-⇒ (RWS-bind m f) ev st pre pf =
  RWS-⇒
    m ev st pre
    (λ r₁ st₁ outs₁ pf₁ x x≡ →
      RWS-⇒
        (f x) ev st₁ (pf₁ x x≡)
        (λ r₂ st₂ outs₂ pf₂ → pf r₂ st₂ (outs₁ ++ outs₂) pf₂))
RWS-⇒ (RWS-gets f) ev st pre pf = pf _ _ _ pre
RWS-⇒ (RWS-put x)  ev st pre pf = pf _ _ _ pre
RWS-⇒ RWS-ask      ev st pre pf = pf _ _ _ pre
RWS-⇒ (RWS-tell x) ev st pre pf = pf _ _ _ pre
RWS-⇒ (RWS-if (otherwise≔ x)) ev st pre pf = RWS-⇒ x ev st pre pf
RWS-⇒ (RWS-if (clause (b ≔ c) cs)) ev st (pre₁ , pre₂) pf =
  (λ pf' → RWS-⇒ c ev st (pre₁ pf') pf)
  , λ pf' → RWS-⇒ (RWS-if cs) ev st (pre₂ pf') pf
proj₁ (RWS-⇒ (RWS-either (Left x) f₁ f₂) ev st (pre₁ , pre₂) pf) x₁ x₁≡ =
  RWS-⇒ (f₁ x₁) ev st (pre₁ x₁ x₁≡) pf
proj₂ (RWS-⇒ (RWS-either (Left x)  f₁ f₂) ev st (pre₁ , pre₂) pf) y ()
proj₁ (RWS-⇒ (RWS-either (Right y) f₁ f₂) ev st (pre₁ , pre₂) pf) y₁ ()
proj₂ (RWS-⇒ (RWS-either (Right y) f₁ f₂) ev st (pre₁ , pre₂) pf) y₁ y₁≡ =
  RWS-⇒ (f₂ y₁) ev st (pre₂ y₁ y₁≡) pf
RWS-⇒ (RWS-ebind m f) ev st pre pf =
  RWS-⇒ m ev st pre
        (λ { (Left x₁) st₁ outs x → pf _ _ _ x
             ; (Right y) st₁ outs x → λ c x₁ →
                 RWS-⇒ (f c) ev st₁ (x c x₁) (λ r st₂ outs₁ x₂ → pf r st₂ (outs ++ outs₁) x₂) })
proj₁ (RWS-⇒ (RWS-maybe x m f) ev st (pre₁ , pre₂) pf) ≡nothing = RWS-⇒ m ev st (pre₁ ≡nothing) pf
proj₂ (RWS-⇒ (RWS-maybe x m f) ev st (pre₁ , pre₂) pf) b b≡     = RWS-⇒ (f b) ev st (pre₂ b b≡) pf

RWS-⇒-bind
  : ∀ {P : RWS-Post Wr St A}
      {Q : RWS-Post Wr St B}
    → {f : A → RWS Ev Wr St B}
    → ∀ m ev st
    → RWS-weakestPre m P ev st
    → RWS-Post-⇒ P (RWS-weakestPre-bindPost ev f Q)
    → RWS-weakestPre (RWS-bind m f) Q ev st
RWS-⇒-bind m ev st con pf =
     RWS-⇒ m ev st con pf

RWS-⇒-ebind
  : ∀ {P : RWS-Post Wr St (Either C A)}
      {Q : RWS-Post Wr St (Either C B)}
    → {f : A → RWS Ev Wr St (Either C B)}
    → ∀ m ev st
    → RWS-weakestPre m P ev st
    → RWS-Post-⇒ P (RWS-weakestPre-ebindPost ev f Q)
    → RWS-weakestPre (RWS-ebind m f) Q ev st
RWS-⇒-ebind m ev st con pf =
  RWS-⇒ m ev st con pf
