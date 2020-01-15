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
  postulate
    VoteOrder : Set
    _<VO_     : VoteOrder → VoteOrder → Set

  -- An 'EpochConfig' carries the information we need tot
  -- survive at most 'bizF' byzantine failures. for now, this is
  -- only a lower bound on the number of overal authors.
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

