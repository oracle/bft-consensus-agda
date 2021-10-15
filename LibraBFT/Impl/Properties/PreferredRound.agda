{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
import      LibraBFT.Concrete.Properties.Common         as Common
import      LibraBFT.Concrete.Properties.PreferredRound as PR
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.Network            as Network
open import LibraBFT.Impl.Consensus.Network.Properties as NetworkProps
open import LibraBFT.Impl.Consensus.RoundManager
import      LibraBFT.Impl.Handle                       as Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Impl.IO.OBM.InputOutputHandlers
open import LibraBFT.Impl.IO.OBM.Properties.InputOutputHandlers
open import LibraBFT.Impl.Properties.Common
open        ReachableSystemStateProps
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open Invariants
open RoundManagerTransProps

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

open        ParamsWithInitAndHandlers Handle.InitHandler.InitAndHandlers
open import LibraBFT.ImplShared.Util.HashCollisions Handle.InitHandler.InitAndHandlers

open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms
                               Handle.InitHandler.InitAndHandlers
                               PeerCanSignForPK PeerCanSignForPK-stable
open        Structural impl-sps-avp

-- This module proves the two "PreferredRound" proof obligations for our handler.

module LibraBFT.Impl.Properties.PreferredRound (𝓔 : EpochConfig) where

postulate -- TODO-2: prove
  preferredRound₁ : PR.ImplObligation₁ Handle.InitHandler.InitAndHandlers 𝓔

-- This proof is essentially the same as the votesOnce₂: no handler sends two different Votes
-- TODO-2: refactor for DRY?
preferredRound₂ : PR.ImplObligation₂ Handle.InitHandler.InitAndHandlers 𝓔
preferredRound₂ _ (step-init initSucc uni) _ _ m∈acts = ⊥-elim (obm-dangerous-magic' "Use the Contract for init handler.")
preferredRound₂ {pid}{pk = pk}{pre} rss (step-msg{sndr , m“} m“∈pool ini) {v = v}{v' = v'} hpk v⊂m m∈acts sig ¬bootstrap ¬msb4 pcsfpk v'⊂m' m'∈acts sig' ¬bootstrap' ¬msb4' _ _ round<
   with v⊂m
...| vote∈qc vs∈qc v≈rbld qc∈m rewrite cong _vSignature v≈rbld =
       ⊥-elim ∘′ ¬msb4 $ qcVoteSigsSentB4-handle pid rss (step-msg m“∈pool ini) m∈acts qc∈m sig vs∈qc v≈rbld ¬bootstrap
...| vote∈vm
  with v'⊂m'
...| vote∈qc vs∈qc' v≈rbld' qc∈m' rewrite cong _vSignature v≈rbld' =
       ⊥-elim ∘′ ¬msb4' $ qcVoteSigsSentB4-handle pid rss (step-msg m“∈pool ini) m'∈acts qc∈m' sig' vs∈qc' v≈rbld' ¬bootstrap'
...| vote∈vm
  with m“
...| P pm = ⊥-elim (<⇒≢ round< (cong (_^∙ vRound) v≡v'))
  where
  hpPool = msgPool pre
  hpPre  = peerStates pre pid
  hpOut  = LBFT-outs (handleProposal 0 pm) hpPre
  open handleProposalSpec.Contract (handleProposalSpec.contract! 0 pm hpPool hpPre)

  v≡v' : v ≡ v'
  v≡v'
    with BlockId-correct? (pm ^∙ pmProposal)
  ...| no ¬validProposal = ⊥-elim (sendVote∉actions {outs = hpOut} {st = hpPre} (sym (proj₂ $ invalidProposal ¬validProposal)) m∈acts)
  ...| yes refl
    with voteAttemptCorrect refl (nohc rss m“∈pool pid ini (invariantsCorrect pid pre ini rss) refl refl   )
  ...| Voting.mkVoteAttemptCorrectWithEpochReq (Left (_ , Voting.mkVoteUnsentCorrect noVoteMsgOuts _)) _ =
    ⊥-elim (sendVote∉actions{outs = hpOut}{st = hpPre} (sym noVoteMsgOuts) m∈acts)
  ...| Voting.mkVoteAttemptCorrectWithEpochReq (Right (Voting.mkVoteSentCorrect vm pid voteMsgOuts _)) _ = begin
    v            ≡⟨        cong (_^∙ vmVote) (sendVote∈actions{outs = hpOut}{st = hpPre} (sym voteMsgOuts) m∈acts) ⟩
    vm ^∙ vmVote ≡⟨ (sym $ cong (_^∙ vmVote) (sendVote∈actions{outs = hpOut}{st = hpPre} (sym voteMsgOuts) m'∈acts)) ⟩
    v'           ∎
    where
    open ≡-Reasoning
... | V vm = ⊥-elim (sendVote∉actions{outs = hvOut}{st = hvPre} (sym noVotes) m∈acts)
  where
  hvPre = peerStates pre pid
  hvOut = LBFT-outs (handle pid (V vm) 0) hvPre
  open handleVoteSpec.Contract (handleVoteSpec.contract! 0 vm (msgPool pre) hvPre)
