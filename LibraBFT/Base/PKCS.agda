open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Base.Encode


module LibraBFT.Base.PKCS where

 postulate 
   signature-size : ℕ

 Signature : Set
 Signature = Σ ByteString (λ s → length s ≡ signature-size)

 postulate
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

 -- A value of a datatype C can have its signature
 -- verified; A value of type WithVerSig c is a proof of that.
 -- Hence; the set (Σ C WithVerSig) is the set of values of
 -- type C with verified signatures.
 record WithVerSig {C : Set} ⦃ ws : WithSig C ⦄ (c : C) : Set where
   field
     isSigned  : Signed c
     verWithPK : PK
     verified  : verify (signableFields c) (signature c isSigned) verWithPK
               ≡ true
 open WithVerSig public

 verCast : {C : Set} ⦃ ws : WithSig C ⦄ {c : C} {is1 is2 : Signed c} {pk1 pk2 : PK}
         → verify (signableFields c) (signature c is1) pk1 ≡ true
         → pk1 ≡ pk2
         → is1 ≡ is2
         → verify (signableFields c) (signature c is2) pk2 ≡ true
 verCast prf refl refl = prf 

 withVerSig-≡ : {C : Set} ⦃ ws : WithSig C ⦄ {c : C}
              → {wvs1 : WithVerSig c}
              → {wvs2 : WithVerSig c}
              → isSigned  wvs1 ≡ isSigned  wvs2
              → verWithPK wvs1 ≡ verWithPK wvs2
              → wvs1 ≡ wvs2
 withVerSig-≡ {wvs1 = wvs1} {wvs2 = wvs2} refl refl
    with verified wvs2 | inspect verified wvs2 | verCast (verified wvs1) refl refl
 ...| vwvs2 | [ R ] | vwvs1 rewrite verify-pi vwvs1 vwvs2 | sym R = refl

 withVerSig-pi : {C : Set} {c : C} ⦃ ws : WithSig C ⦄
               → (wvs1 : WithVerSig c)
               → (wvs2 : WithVerSig c)
               → wvs2 ≡ wvs1
 withVerSig-pi {C} {c} ⦃ ws ⦄ wvs2 wvs1
    with isSigned? c
 ...| no ¬Signed = ⊥-elim (¬Signed (isSigned wvs1))
 ...| yes sc
    with verWithPK wvs1 ≟PK verWithPK wvs2
 ...| no  neq = ⊥-elim (neq (verify-pk-inj {signableFields c}
                                           (verified wvs1)
                                           (subst (λ is → verify (signableFields c) (signature c is) (verWithPK wvs2) ≡ true)
                                                  (Signed-pi c (isSigned wvs2) (isSigned wvs1))
                                                  (verified wvs2))))
 ...| yes pks≡ = withVerSig-≡ {wvs1 = wvs1} {wvs2 = wvs2} (Signed-pi c (isSigned wvs1) (isSigned wvs2)) pks≡

 check-signature : {C : Set} ⦃ ws : WithSig C ⦄ → PK → (c : C) → Maybe (WithVerSig c)
 check-signature pk c with isSigned? c
 ...| no  _  = nothing
 ...| yes sc with verify (signableFields c) (signature c sc) pk
                | inspect (verify (signableFields c) (signature c sc)) pk
 ...| false |   _   = nothing
 ...| true  | [ R ] = just (record { isSigned  = sc 
                                   ; verWithPK = pk 
                                   ; verified  = R })

 check-signature-signed : {C : Set} ⦃ ws : WithSig C ⦄
                        → {c : C}
                        → (wvs : WithVerSig c)
                        → Signed c
 check-signature-signed {C} {c = c} wvs = isSigned wvs

 check-signature-pk≡ : {C : Set} {pk : PK} {c : C} ⦃ ws : WithSig C ⦄
                     → (wvs : WithVerSig c)
                     → check-signature pk c ≡ just wvs
                     → verWithPK wvs ≡ pk
 check-signature-pk≡  {pk = pk} {c = c} wvs prf
    with isSigned? c
 ...| no ¬signed = ⊥-elim (¬signed (isSigned wvs))
 ...| yes signed
    with  verify (signableFields c) (signature c signed)  pk | inspect
         (verify (signableFields c) (signature c signed)) pk
 ...| false | [ R ] = ⊥-elim (maybe-⊥ prf refl)
 ...| true  | [ R ] rewrite Signed-pi c signed (isSigned wvs)= verify-pk-inj (verified wvs) R

 check-signature-nothing : {C : Set} {pk : PK} {c : C} ⦃ ws : WithSig C ⦄
                         → check-signature pk c ≡ nothing
                         → ¬ (Signed c) ⊎ Σ (Signed c) (λ x → false ≡ verify (signableFields c) (signature c x) pk)
 check-signature-nothing {pk = pk} {c = c} prf
    with isSigned? c
 ...| no ¬signed = inj₁ ¬signed
 ...| yes signed
    with  verify (signableFields c) (signature c signed) pk | inspect
         (verify (signableFields c) (signature c signed)) pk
 ...| false | [ R ] = inj₂ ( signed , sym R )
 ...| true  | [ R ] = ⊥-elim (maybe-⊥ (sym prf) refl)

 check-signature-≡ : {C : Set} {pk : PK} {c : C} ⦃ ws : WithSig C ⦄
                      → (wvs : WithVerSig c)
                      → verWithPK wvs ≡ pk
                      → check-signature pk c ≡ just wvs
 check-signature-≡ {pk = pk} {c = c} wvs pks≡
    with  check-signature pk  c | inspect
         (check-signature pk) c
 ...| just wvs' | [ R' ] = cong just (withVerSig-pi wvs wvs')
 ...| nothing   | [ R' ]
    with check-signature-nothing R'
 ...| inj₁ ¬signed = ⊥-elim (¬signed (isSigned wvs))
 ...| inj₂ ( signed , ¬ver ) rewrite (sym pks≡) | Signed-pi c signed (isSigned wvs) =
                           ⊥-elim (false≢true (trans ¬ver (verified wvs)))

 check-signature-correct : {C : Set} ⦃ ws : WithSig C ⦄
                         → {c : C}
                         → (wvs : WithVerSig c)
                         → check-signature {C} ⦃ ws ⦄ (verWithPK wvs) c ≡ just wvs
 check-signature-correct {C} {c = c} wvs
    with isSigned? c
 ...| no  notSigned = ⊥-elim (notSigned (isSigned wvs))
 ...| yes sc
    with verify (signableFields c) (signature c sc) (verWithPK wvs)
                | inspect (verify (signableFields c) (signature c sc)) (verWithPK wvs)
 ...| false | [ R ] rewrite Signed-pi c sc (isSigned wvs) = ⊥-elim (false≢true (trans (sym R) (verified wvs)))
 ...| true  | [ R ] = cong just (withVerSig-pi wvs (record { isSigned = sc ; verWithPK = verWithPK wvs ; verified = R }))
