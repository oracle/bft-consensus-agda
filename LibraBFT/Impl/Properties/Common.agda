{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
import      LibraBFT.Concrete.Properties.Common    as Common
import      LibraBFT.Concrete.Properties.VotesOnce as VO
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.Network            as Network
open import LibraBFT.Impl.Consensus.Network.Properties as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager
open import LibraBFT.Impl.Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open StateInvariants
open StateTransProps

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

open        ParamsWithInitAndHandlers InitAndHandlers
open import LibraBFT.ImplShared.Util.HashCollisions InitAndHandlers

open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers
                               PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        Structural impl-sps-avp

-- This module contains definitions and lemmas used by proofs of the
-- implementation obligations for VotesOnce and PreferredRoundRule.

module LibraBFT.Impl.Properties.Common where

postulate -- TODO-2: prove (waiting on: `handle`, refinements to handler contracts)
  -- This will be proved for the implementation, confirming that honest
  -- participants only store QCs comprising votes that have actually been sent.
  -- Votes stored in highesQuorumCert and highestCommitCert were sent before.
  -- Note that some implementations might not ensure this, but LibraBFT does
  -- because even the leader of the next round sends its own vote to itself,
  -- as opposed to using it to construct a QC using its own unsent vote.
  qcVotesSentB4
    : ∀ {pid qc vs pk}{st : SystemState}
      → ReachableSystemState st
      → initialised st pid ≡ initd
      → qc QC.∈RoundManager (peerStates st pid)
      → vs ∈ qcVotes qc
      → ¬ (∈GenInfo-impl genesisInfo (proj₂ vs))
      → MsgWithSig∈ pk (proj₂ vs) (msgPool st)
