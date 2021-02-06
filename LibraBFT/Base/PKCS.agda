{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Base.Encode
open import LibraBFT.Base.ByteString

-- This module contains a model of cryptographic signatures on
-- certain data structures, and creation and verification
-- thereof.  These data structures, defined by the WithVerSig
-- type, can be optionally signed, and if they are signed, the
-- signature covers a ByteString derived from the data structure,
-- enabling support for signature that cover only (functions of)
-- specific parts of the data structure.  The module also
-- contains some properties we have found useful in other
-- contexts, though they are not yet used in this repo.

module LibraBFT.Base.PKCS where

 postulate -- valid assumption
   signature-size : ℕ

 Signature : Set
 Signature = Σ ByteString (λ s → length s ≡ signature-size)

 postulate -- valid assumptions
   PK : Set
   SK : Set
   IsKeyPair : PK → SK → Set
   _≟PK_ : (pk1 pk2 : PK) → Dec (pk1 ≡ pk2)

   instance
     enc-PK    : Encoder PK
     enc-SigMB : Encoder (Maybe Signature)

   sign-raw : ByteString → SK → Signature
   verify   : ByteString → Signature → PK → Bool

   -- We assume no "signature collisions", as represented by verify-pk-inj
   verify-pk-inj : ∀{bs sig pk pk'}
                 → verify bs sig pk  ≡ true
                 → verify bs sig pk' ≡ true
                 → pk ≡ pk'

   verify-bs-inj : ∀{bs bs' sig pk}
                 → verify bs  sig pk ≡ true
                 → verify bs' sig pk ≡ true
                 → bs ≡ bs'

   verify-pi : ∀{bs sig pk}
             → (v1 : verify bs sig pk ≡ true)
             → (v2 : verify bs sig pk ≡ true)
             → v1 ≡ v2

   verify-sign : ∀{bs pk sk}
               → IsKeyPair pk sk
               → verify bs (sign-raw bs sk) pk ≡ true

   verify-fail : ∀{bs pk sk}
               → ¬ IsKeyPair pk sk
               → verify bs (sign-raw bs sk) pk ≡ false

   -- We consider a PK to be (permanently) either honest or not,
   -- respresented by the following postulate.  This is relevant
   -- in reasoning about possible behaviours of a modeled system.
   -- Specifically, the secret key corresponding to an honest PK
   -- is assumed not to be leaked, ensuring that cheaters cannot
   -- forge new signatures for honest PKs.  Furthermore, if a peer
   -- is assigned we use possession
   -- of an honest PK in a given epoch to modelWe will postulate that, among
   -- the PKs chosen for a particular epoch, the number of them
   -- that are dishonest is at most the number of faults to be
   -- tolerated for that epoch.  This definition is /meta/: the
   -- information about which PKs are (dis)honest should never be
   -- used by the implementation -- it is only for modeling and
   -- proofs.
   Meta-Dishonest-PK : PK → Set

   Meta-DishonestPK? : (pk : PK) → Dec (Meta-Dishonest-PK pk)


 Meta-Honest-PK : PK → Set
 Meta-Honest-PK  = ¬_ ∘ Meta-Dishonest-PK

 -- A datatype C might that might carry values with
 -- signatures should be an instance of 'WithSig' below.
 record WithSig (C : Set) : Set₁ where
   field
     -- A decidable predicate indicates whether values have
     -- been signed
     Signed         : C → Set
     Signed-pi      : ∀ (c : C)
                    → (is1 : Signed c)
                    → (is2 : Signed c)
                    → is1 ≡ is2
     isSigned?      : (c : C) → Dec (Signed c)

     -- Signed values must have a signature
     signature      : (c : C)(hasSig : Signed c) → Signature

     -- All values must be /encoded/ into a ByteString that
     -- is supposed to be verified against a signature.
     signableFields : C → ByteString
 open WithSig {{...}} public

 sign : {C : Set} ⦃ ws : WithSig C ⦄ → C → SK → Signature
 sign c = sign-raw (signableFields c)

 Signature≡ : {C : Set} ⦃ ws : WithSig C ⦄ → C → Signature → Set
 Signature≡ c sig = Σ (Signed c) (λ s → signature c s ≡ sig)

 -- A value of a datatype C can have its signature
 -- verified; A value of type WithVerSig c is a proof of that.
 -- Hence; the set (Σ C WithVerSig) is the set of values of
 -- type C with verified signatures.
 record WithVerSig {C : Set} ⦃ ws : WithSig C ⦄ (pk : PK) (c : C) : Set where
   constructor mkWithVerSig
   field
     isSigned  : Signed c
     verified  : verify (signableFields c) (signature c isSigned) pk
               ≡ true
 open WithVerSig public

 ver-signature : ∀{C pk}⦃ ws : WithSig C ⦄{c : C} → WithVerSig pk c → Signature
 ver-signature {c = c} wvs = signature c (isSigned wvs)

 verCast : {C : Set} ⦃ ws : WithSig C ⦄ {c : C} {is1 is2 : Signed c} {pk1 pk2 : PK}
         → verify (signableFields c) (signature c is1) pk1 ≡ true
         → pk1 ≡ pk2
         → is1 ≡ is2
         → verify (signableFields c) (signature c is2) pk2 ≡ true
 verCast prf refl refl = prf

 wvsCast : {C : Set} ⦃ ws : WithSig C ⦄ {c : C} {pk1 pk2 : PK}
         → WithVerSig pk1 c
         → pk2 ≡ pk1
         → WithVerSig pk2 c
 wvsCast {c = c} wvs refl = wvs

 withVerSig-≡ : {C : Set} ⦃ ws : WithSig C ⦄ {pk : PK} {c : C}
              → {wvs1 : WithVerSig pk c}
              → {wvs2 : WithVerSig pk c}
              → isSigned  wvs1 ≡ isSigned  wvs2
              → wvs1 ≡ wvs2
 withVerSig-≡ {wvs1 = wvs1} {wvs2 = wvs2} refl
    with verified wvs2 | inspect verified wvs2 | verCast (verified wvs1) refl refl
 ...| vwvs2 | [ R ] | vwvs1 rewrite verify-pi vwvs1 vwvs2 | sym R = refl

 withVerSig-pi : {C : Set} {pk : PK} {c : C} ⦃ ws : WithSig C ⦄
               → (wvs1 : WithVerSig pk c)
               → (wvs2 : WithVerSig pk c)
               → wvs2 ≡ wvs1
 withVerSig-pi {C} {pk} {c} ⦃ ws ⦄ wvs2 wvs1
    with isSigned? c
 ...| no ¬Signed = ⊥-elim (¬Signed (isSigned wvs1))
 ...| yes sc = withVerSig-≡ {wvs1 = wvs1} {wvs2 = wvs2} (Signed-pi c (isSigned wvs1) (isSigned wvs2))

 data SigCheckResult {C : Set} ⦃ ws : WithSig C ⦄ (pk : PK) (c : C) : Set where
   notSigned   : ¬ Signed c → SigCheckResult pk c
   checkFailed : (sc : Signed c) → verify (signableFields c) (signature c sc) pk ≡ false → SigCheckResult pk c
   sigVerified : WithVerSig pk c → SigCheckResult pk c

 checkFailed≢sigVerified : {C : Set} ⦃ ws : WithSig C ⦄ {pk : PK} {c : C}
                           {wvs : WithVerSig ⦃ ws ⦄ pk c}
                           {sc : Signed c} {v : verify (signableFields c) (signature c sc) pk ≡ false}
                         → checkFailed sc v ≡ sigVerified wvs → ⊥
 checkFailed≢sigVerified ()

 data SigCheckOutcome : Set where
   notSigned   : SigCheckOutcome
   checkFailed : SigCheckOutcome
   sigVerified : SigCheckOutcome

 data SigCheckFailed : Set where
   notSigned   : SigCheckFailed
   checkFailed : SigCheckFailed

 check-signature : {C : Set} ⦃ ws : WithSig C ⦄ → (pk : PK) → (c : C) → SigCheckResult pk c
 check-signature pk c with isSigned? c
 ...| no  ns  = notSigned ns
 ...| yes sc with verify (signableFields c) (signature c sc) pk
                | inspect (verify (signableFields c) (signature c sc)) pk
 ...| false | [ nv ] = checkFailed sc nv
 ...| true  | [ v  ] = sigVerified (record { isSigned  = sc
                                           ; verified  = v })

 sigCheckOutcomeFor : {C : Set} ⦃ ws : WithSig C ⦄ (pk : PK) (c : C) → SigCheckOutcome
 sigCheckOutcomeFor pk c with check-signature pk c
 ...| notSigned _     = notSigned
 ...| checkFailed _ _ = checkFailed
 ...| sigVerified _   = sigVerified

 sigVerifiedVerSigCS : {C : Set} ⦃ ws : WithSig C ⦄ {pk : PK} {c : C}
                     → sigCheckOutcomeFor pk c ≡ sigVerified
                     → ∃[ wvs ] (check-signature ⦃ ws ⦄ pk c ≡ sigVerified wvs)
 sigVerifiedVerSigCS {pk = pk} {c = c} prf
    with  check-signature pk  c | inspect
         (check-signature pk) c
 ...| sigVerified verSig | [ R ] rewrite R =  verSig , refl

 sigVerifiedVerSig : {C : Set} ⦃ ws : WithSig C ⦄ {pk : PK} {c : C}
                   → sigCheckOutcomeFor pk c ≡ sigVerified
                   → WithVerSig pk c
 sigVerifiedVerSig = proj₁ ∘ sigVerifiedVerSigCS

 sigVerifiedSCO : {C : Set} ⦃ ws : WithSig C ⦄ {pk : PK} {c : C}
                   → (wvs : WithVerSig pk c)
                   → sigCheckOutcomeFor pk c ≡ sigVerified
 sigVerifiedSCO {pk = pk} {c = c} wvs
   with check-signature pk c
 ...| notSigned  ns      = ⊥-elim (ns (isSigned wvs))
 ...| checkFailed xx xxs rewrite Signed-pi c xx (isSigned wvs) = ⊥-elim (false≢true (trans (sym xxs) (verified wvs)))
 ...| sigVerified wvs' = refl

 failedSigCheckOutcome : {C : Set} ⦃ ws : WithSig C ⦄ (pk : PK) (c : C)
                       → sigCheckOutcomeFor pk c ≢ sigVerified
                       → SigCheckFailed
 failedSigCheckOutcome pk c prf with sigCheckOutcomeFor pk c
 ...| notSigned   = notSigned
 ...| checkFailed = checkFailed
 ...| sigVerified = ⊥-elim (prf refl)
