open import Data.Maybe
open import Data.Nat
import      LibraBFT.Abstract.Records as Abs
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Prelude

-- These types should eventually mirror Libra/Consensus/Types.hs

module LibraBFT.Concrete.Types where

  data Epoch : Set where
    mkEpoch : ∀ (eId : ℕ) → Epoch

  record QuorumCert : Set where
    field
      qcVoteData : ℕ           -- TODO: these are just placeholders; fill out types
      qcSignedLedgerInfo : ℕ

  record BlockData {ℓ} (a : Set ℓ) : Set ℓ where
    field
      bdEpoch      : Epoch
      bdRound      : Round
      -- bdTimestamp  : Instant
      bdQuorumCert : QuorumCert
      bdBlockTempXX : a
      -- TODOv3:
      -- bdBlockType  : BlockType a

  record Block {ℓ} (a : Set ℓ) : Set ℓ where
    constructor block
    field
      bId        : BlockHash
      bBlockData : BlockData a
      bSignature : Maybe Signature

  postulate
    getBlockRound       : ∀ {ℓ}{a} → Block {ℓ} a → Round
    getBlockEpochId     : ∀ {ℓ}{a} → Block {ℓ} a → EpochId
    getBlockAuthor      : ∀ {ℓ}{a} → (b : Block {ℓ} a) → NodeId
    getBlockQC          : ∀ {ℓ}{a} → Block {ℓ} a → QuorumCert
    getBlockCommand     : ∀ {ℓ}{a} → Block {ℓ} a → a
  -- This is (supposed to be) the moral equivalent of deriving Serialize (Block a) given Serialize a.

  -- TODO: actually it's not because I failed to make it that way, and just postulated the Encoder
  -- of the whole thing, with no assumptions about a.  Would be nice to do that the right way,
  -- whatever that is :-).
  postulate
    instance
      blockEncoder : ∀ {ℓ}{a : Set ℓ} → Encoder (Block a)
      qcEncoder    : Encoder QuorumCert
