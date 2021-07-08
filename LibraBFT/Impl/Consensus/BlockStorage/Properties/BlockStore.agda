{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote as Vote
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Consensus.BlockStorage.Properties.BlockStore where

module executeAndInsertBlockESpec {𝓔 : EpochConfig} (bs : BlockStore) (b : Block) where
  postulate
    ebBlock≡ : ∀ {bs' eb} → executeAndInsertBlockE bs b ≡ Right (bs' , eb) → eb ^∙ ebBlock ≡ b

module syncInfoMSpec where
  syncInfo : RoundManager → SyncInfo
  syncInfo pre =
    SyncInfo∙new ((_rmEC pre) ^∙ lBlockStore ∙ bsHighestQuorumCert)
                 ((_rmEC pre) ^∙ lBlockStore ∙ bsHighestCommitCert)

  -- This exposes an issue with lBlockStore, which is defined in the Haskell code as
  --
  --   Lens RoundManager BlockStore
  --
  -- (indirectly, via an instance of RWBlockStore), but so far is defined here as
  --
  --   Lens RoundManagerEC BlockStore
  --
  -- We need to figure out how to deal with updating things that can affect either the
  -- RoundManagerEC-correct or the RoundManagerWithMetaEC field).  In the general case, this is
  -- going to require application-specific proof that modifying the BlockStore results in a state
  -- for which those fields can be constructed.  We can construct various cases in which there is no
  -- change and have lenses via RMLens.  However, for cases that do change those fields, we might
  -- not be able to have Lens because we will need to construct those fields.  Or maybe we will need
  -- another class that we can have instances of that provide the appropriate fields.  In any case,
  -- we might need to avoid using Lenses in some cases, and instead use something like
  -- rmSetBlockStore.
  
  contract : ∀ pre Post → (Post (syncInfo pre) pre []) → LBFT-weakestPre syncInfoM Post pre
  contract pre Post pf  = λ ._ refl ._ refl ._ refl ._ refl → {!pf!}

  -- ._ refl .unit refl .unit refl = pf
