open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import Optics.All

-- This module proves that the insertion functions from
-- LibraBFT.Concrete.BlockTreeAbstraction preserve the
-- necessary invariants. This proofs require knowledge of
-- the system layer, hence, I placed them in the Global
-- folder.
module LibraBFT.Global.BlockTreeInvariants
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
    (ec      : Meta EpochConfig)
    -- We might need some system level info!
    -- (sys : ParticularPropertiesOfTheSystemModel)
 where

  open import LibraBFT.Concrete.Util.KVMap
    renaming (empty to KV-empty)
  open import LibraBFT.Concrete.NetworkMsg

  open import LibraBFT.Concrete.Consensus.Types.EpochIndep
  open import LibraBFT.Concrete.Consensus.Types.EpochDep ec
  open import LibraBFT.Concrete.BlockTreeAbstraction hash hash-cr ec

  -- Bring in record-chains for records inside a BlockTree.
  open import LibraBFT.Abstract.RecordChain ec UID _≟UID_ ⦃ abstractBT ⦄
