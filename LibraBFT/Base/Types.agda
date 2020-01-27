open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode

-- Exposition of the ground types that we build our abstract reasoning
-- over. 
module LibraBFT.Base.Types where

  EpochId : Set
  EpochId = ℕ

  -- A node is a participant in the system. 
  NodeId : Set
  NodeId = ℕ

  Round : Set
  Round = ℕ

  Command : Set
  Command = ℕ

  QCHash : Set
  QCHash = Hash

  BlockHash : Set
  BlockHash = Hash

  State : Set
  State = Hash

  NonInjective : ∀{a b}{A : Set a}{B : Set b}
               → (A → B) → Set (a ℓ⊔ b)
  NonInjective {A = A} f = Σ (A × A) (λ { (x₁ , x₂) → x₁ ≢ x₂ × f x₁ ≡ f x₂ })

  NonInjective-∘ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
                 → {f : A → B}(g : B → C)
                 → NonInjective f
                 → NonInjective (g ∘ f)
  NonInjective-∘ g ((x0 , x1) , (x0≢x1 , fx0≡fx1)) 
    = ((x0 , x1) , x0≢x1 , (cong g fx0≡fx1))


  -- VCM: After our discussion about vote order; I propose
  -- we make it into a postulate. Naturally, as the name suggests,
  -- it must have some sort of order raltion; also inacessible.

  -- MSM: But then how can we create values of this type in the concrete model?
  --      I am making it ℕ for now.  Of course, this makes it accessible to those
  --      that shouldn't access it, but I think that should be addressed by convention,
  --      e.g. naming fields of this type with an AUX suffix, enabling searching and
  --      careful examination of each use to ensure it's not accessed where it shouldn't be.

  {- 
  postulate
    VoteOrder : Set
    _<VO_     : VoteOrder → VoteOrder → Set
   -}
  VoteOrder : Set
  VoteOrder = ℕ

  _<VO_     : VoteOrder → VoteOrder → Set
  _<VO_ = _<_

  -- An 'EpochConfig' carries the information we need to
  -- survive at most 'bizF' byzantine failures.
  record EpochConfig : Set where
    field
      epochId  : EpochId
      authorsN : ℕ
      bizF     : ℕ

      isBFT    : authorsN ≥ suc (3 * bizF)

      seed     : ℕ

      ecInitialState  : State
  
      initialAgreedHash : Hash

    QuorumSize : ℕ
    QuorumSize = authorsN ∸ bizF

    Author     : Set
    Author     = Fin authorsN
  open EpochConfig public

  -- TODO: eventually we will want to associate PKs with all participants, not just those of the
  -- current epoch.  This is so we can verify signatures on fraudulent messages pretending to be
  -- authors of an epoch for accountability reasons, and also because that's what libra does.

  -- Public Key Infrastructure for a given epoch.
  record PKI (ec : EpochConfig) : Set where
    field
      isAuthor : NodeId -> Maybe (Author ec)
      pkAuthor : Author ec -> PK
      pkInj    : ∀ (a₁ a₂ : Author ec)  -- Authors must have distinct public keys, otherwise a
                                        -- dishonest author can potentially impersonate an honest
                                        -- author.
               → pkAuthor a₁ ≡ pkAuthor a₂
               → a₁ ≡ a₂
  open PKI public

  -- Create an EpochConfig for each epoch.  This is just for testing and facilitating progress on
  -- other stuff.

  fakeAuthorsN : ℕ
  fakeAuthorsN = 4

  fakeAuthors : NodeId → Maybe (Fin fakeAuthorsN)
  fakeAuthors nid with nid <? fakeAuthorsN
  ...| yes xx = just (fromℕ≤ xx)
  ...| no  _  = nothing

  postulate
    fakeNodeIdPK : NodeId → PK
    fakePKs      : Fin fakeAuthorsN → PK
    fakePKsInj   : (x x₁ : Fin 4) (x₂ : fakePKs x ≡ fakePKs x₁) → x ≡ x₁

  fakeEC : EpochId → EpochConfig
  fakeEC eid = record {
                 epochId           = eid
               ; authorsN          = fakeAuthorsN
               ; bizF              = 1
               ; isBFT             = s≤s (s≤s (s≤s (s≤s z≤n)))
               ; seed              = 0
               ; ecInitialState    = dummyHash
               ; initialAgreedHash = dummyHash

               }

  postulate
    fakePKI : (ec : EpochConfig) → PKI ec
