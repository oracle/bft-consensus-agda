{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.Types
open import LibraBFT.Base.PKCS
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle
open        EpochConfig
open import LibraBFT.Yasm.Base ℓ-RoundManager

-- In this module, we instantiate the system model with parameters to
-- model a system using the simple implementation model we have so
-- far, which aims to obey the VotesOnceRule, but not PreferredRoundRule
-- yet.  This will evolve as we build out a model of a real
-- implementation.

module LibraBFT.Concrete.System.Parameters where
 ConcSysParms : SystemParameters
 ConcSysParms = mkSysParms
                 NodeId
                 _≟NodeId_
                 GenesisInfo
                 genInfo
                 RoundManager
                 initRM
                 NetworkMsg
                 Vote
                 sig-Vote
                 _⊂Msg_
                 ∈GenInfo
                 initWrapper
                 peerStep

 open import LibraBFT.Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms

 -- What EpochConfigs are known in the system?  For now, only the
 -- initial one.  Later, we will add knowledge of subsequent
 -- EpochConfigs known via EpochChangeProofs.  In fact, the
 -- implementation creates and stores and EpochChangeProof even for the
 -- initial epoch, so longer term just the inECP constructor may suffice.
 data EpochConfig∈Sys (st : SystemState) (𝓔 : EpochConfig) : Set ℓ-EC where
   inGenInfo : init-EC genInfo ≡ 𝓔 → EpochConfig∈Sys st 𝓔
   -- inECP  : ∀ {ecp} → ecp ECP∈Sys st → verify-ECP ecp 𝓔 → EpochConfig∈Sys

 -- A peer pid can sign a new message for a given PK if pid is the owner of a PK in a known
 -- EpochConfig.
 record PeerCanSignForPK (st : SystemState) (v : Vote) (pid : NodeId) (pk : PK) : Set ℓ-VSFP where
   constructor mkPCS4PK
   field
     𝓔       : EpochConfig
     𝓔id≡    : epoch 𝓔 ≡ v ^∙ vEpoch
     𝓔inSys  : EpochConfig∈Sys st 𝓔
     mbr      : Member 𝓔
     nid≡     : toNodeId  𝓔 mbr ≡ pid
     pk≡      : getPubKey 𝓔 mbr ≡ pk
 open PeerCanSignForPK

 PCS4PK⇒NodeId-PK-OK : ∀ {st v pid pk} → (pcs : PeerCanSignForPK st v pid pk) → NodeId-PK-OK (𝓔 pcs) pk pid
 PCS4PK⇒NodeId-PK-OK (mkPCS4PK _ _ _ mbr n≡ pk≡) = mbr , n≡ , pk≡

 -- This is super simple for now because the only known EpochConfig is dervied from genInfo, which is not state-dependent
 PeerCanSignForPK-stable : ValidSenderForPK-stable-type PeerCanSignForPK
 PeerCanSignForPK-stable _ _ (mkPCS4PK 𝓔₁ 𝓔id≡₁ (inGenInfo refl) mbr₁ nid≡₁ pk≡₁) = (mkPCS4PK 𝓔₁ 𝓔id≡₁ (inGenInfo refl) mbr₁ nid≡₁ pk≡₁)
