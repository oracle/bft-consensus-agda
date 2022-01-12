{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Util.Crypto
open import Optics.All
open import Util.PKCS
open import Util.Prelude

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open        EpochConfig
open import Yasm.Base ℓ-RoundManager

-- In this module, we instantiate the system model with parameters to
-- model a system using the simple implementation model we have so
-- far, which aims to obey the VotesOnceRule, but not PreferredRoundRule
-- yet.  This will evolve as we build out a model of a real
-- implementation.

module LibraBFT.Concrete.System.Parameters where
 ConcSysParms : SystemTypeParameters
 ConcSysParms = mkSysTypeParms
                 NodeId
                 _≟NodeId_
                 BootstrapInfo
                 ∈BootstrapInfo-impl
                 RoundManager
                 NetworkMsg
                 Vote         -- TODO-3: This should be a type that also allows Block, because
                              -- NetworkMsgs can include signed Blocks, raising the possibility of
                              -- the "masquerading" issue mentioned in
                              -- LibraBFT.ImplShared.Util.Crypto, which we will need to address by
                              -- using HashTags, as also discussed in the module.
                 sig-Vote
                 _⊂Msg_

 open import Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms

 module ParamsWithInitAndHandlers (iiah : SystemInitAndHandlers ConcSysParms) where
   open SystemInitAndHandlers iiah
   open WithInitAndHandlers iiah

   -- What EpochConfigs are known in the system?  For now, only the
   -- initial one.  Later, we will add knowledge of subsequent
   -- EpochConfigs known via EpochChangeProofs.  In fact, the
   -- implementation creates and stores and EpochChangeProof even for the
   -- initial epoch, so longer term just the inECP constructor may suffice.
   data EpochConfig∈Sys (st : SystemState) (𝓔 : EpochConfig) : Set ℓ-EC where
     inBootstrapInfo : init-EC bootstrapInfo ≡ 𝓔 → EpochConfig∈Sys st 𝓔
     -- inECP  : ∀ {ecp} → ecp ECP∈Sys st → verify-ECP ecp 𝓔 → EpochConfig∈Sys

   -- This is trivial for now, but will be nontrivial when we support epoch change
   𝓔-∈sys-injective : ∀ {st 𝓔₁ 𝓔₂}
                      → EpochConfig∈Sys st 𝓔₁
                      → EpochConfig∈Sys st 𝓔₂
                      → epoch 𝓔₁ ≡ epoch 𝓔₂
                      → 𝓔₁ ≡ 𝓔₂
   𝓔-∈sys-injective (inBootstrapInfo refl) (inBootstrapInfo refl) refl = refl

   -- A peer pid can sign a new message for a given PK if pid is the owner of a PK in a known
   -- EpochConfig.
   record PeerCanSignForPKinEpoch (st : SystemState) (v : Vote) (pid : NodeId) (pk : PK)
                                  (𝓔 : EpochConfig) (𝓔inSys : EpochConfig∈Sys st 𝓔)
                                  : Set ℓ-VSFP where
     constructor mkPCS4PKin𝓔
     field
       𝓔id≡    : epoch 𝓔 ≡ v ^∙ vEpoch
       mbr      : Member 𝓔
       nid≡     : toNodeId  𝓔 mbr ≡ pid
       pk≡      : getPubKey 𝓔 mbr ≡ pk
   open PeerCanSignForPKinEpoch

   record PeerCanSignForPK (st : SystemState) (v : Vote) (pid : NodeId) (pk : PK) : Set ℓ-VSFP where
     constructor mkPCS4PK
     field
       pcs4𝓔     : EpochConfig
       pcs4𝓔∈Sys : EpochConfig∈Sys st pcs4𝓔
       pcs4in𝓔   : PeerCanSignForPKinEpoch st v pid pk pcs4𝓔 pcs4𝓔∈Sys
   open PeerCanSignForPK

   PCS4PK⇒NodeId-PK-OK : ∀ {st v pid pk 𝓔 𝓔∈Sys} → (pcs : PeerCanSignForPKinEpoch st v pid pk 𝓔 𝓔∈Sys) → NodeId-PK-OK 𝓔 pk pid
   PCS4PK⇒NodeId-PK-OK (mkPCS4PKin𝓔 _ mbr n≡ pk≡) = mbr , n≡ , pk≡

   -- This is super simple for now because the only known EpochConfig is dervied from bootstrapInfo, which is not state-dependent
   PeerCanSignForPK-stable : ValidSenderForPK-stable-type PeerCanSignForPK
   PeerCanSignForPK-stable _ _ (mkPCS4PK 𝓔₁ (inBootstrapInfo refl) (mkPCS4PKin𝓔 𝓔id≡₁ mbr₁ nid≡₁ pk≡₁)) =
                               (mkPCS4PK 𝓔₁ (inBootstrapInfo refl) (mkPCS4PKin𝓔 𝓔id≡₁ mbr₁ nid≡₁ pk≡₁))

   peerCanSignEp≡ : ∀ {pid v v' pk s'}
                  → PeerCanSignForPK s' v pid pk
                  → v ^∙ vEpoch ≡ v' ^∙ vEpoch
                  → PeerCanSignForPK s' v' pid pk
   peerCanSignEp≡ (mkPCS4PK 𝓔₁ 𝓔inSys₁ (mkPCS4PKin𝓔 𝓔id≡₁ mbr₁ nid≡₁ pk≡₁)) refl
     = (mkPCS4PK 𝓔₁ 𝓔inSys₁ (mkPCS4PKin𝓔 𝓔id≡₁ mbr₁ nid≡₁ pk≡₁))
