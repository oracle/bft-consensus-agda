{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Optics.All
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS

open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Properties.Aux

open import LibraBFT.Concrete.System impl-sps-avp
open import LibraBFT.Concrete.System.Parameters
import      LibraBFT.Concrete.Properties.VotesOnce as VO

open import LibraBFT.Yasm.AvailableEpochs as AE
open import LibraBFT.Yasm.Base
open import LibraBFT.Yasm.System     ConcSysParms
open import LibraBFT.Yasm.Properties ConcSysParms
open        Structural impl-sps-avp

open import LibraBFT.Concrete.Obligations

-- In this module, we (will) prove the two implementation obligations for the VotesOnce rule.  Note
-- that it is not yet 100% clear that the obligations are the best definitions to use.  See comments
-- in Concrete.VotesOnce.  We will want to prove these obligations for the fake/simple
-- implementation (or some variant on it) and streamline the proof before we proceed to tacke more
-- ambitious properties.

module LibraBFT.Impl.Properties.VotesOnce where

  postulate  -- TODO : prove
    newVoteSameEpochGreaterRound : ∀ {e 𝓔s pid pool ms s s' outs v m pk}
                                 → StepPeerState {e} pid 𝓔s pool ms s' outs
                                 → ms ≡ just s
                                 → v  ⊂Msg m → m ∈ outs → (sig : WithVerSig pk v)
                                 → ¬ MsgWithSig∈ pk (ver-signature sig) pool
                                 → (v ^∙ vEpoch) ≡ (₋epEC s) ^∙ epEpoch
                                 × suc ((₋epEC s) ^∙ epLastVotedRound) ≡ (v ^∙ vRound)  -- New vote for higher round than last voted
                                 × (v ^∙ vRound) ≡ ((₋epEC s') ^∙ epLastVotedRound)     -- Last voted round is round of new vote

    noEpochChangeYet : ∀ {e pid 𝓔s pool outs ps' ps}
                     → StepPeerState {e} pid 𝓔s pool (just ps') ps outs
                     → (₋epEC ps) ^∙ epEpoch ≡ (₋epEC ps') ^∙ epEpoch

    lastVoteRound-mono : ∀ {e pid 𝓔s pool outs ps' ps}
                       → StepPeerState {e} pid 𝓔s pool (just ps') ps outs
                       → (₋epEC ps') ^∙ epEpoch ≡ (₋epEC ps) ^∙ epEpoch  -- Always true, so far, as no epoch changes.
                       → (₋epEC ps') ^∙ epLastVotedRound ≤ (₋epEC ps) ^∙ epLastVotedRound

    noMsgsByUninitialised : ∀ {e} {st : SystemState e} {pid} {m}
                          → ReachableSystemState st
                          → (pid , m) ∈ msgPool st
                          → Is-just (Map-lookup pid (peerStates st))

  firstSendEstablishes : Vote → PK → SystemStateRel Step
  firstSendEstablishes _ _ (step-epoch _) = ⊥ 
  firstSendEstablishes _ _ (step-peer (step-cheat _ _)) = ⊥
  firstSendEstablishes v' pk {e} {.e} sysStep@(step-peer {pid = pid'} {pre = pre} pstep@(step-honest {st = pst} {outs} _)) =
    let post = StepPeer-post pstep
     in Map-lookup pid' (peerStates post) ≡ just pst
      × Σ (IsValidNewPart (₋vSignature v') pk sysStep)
          λ ivnp → let (_ , (_ , vpb)) = ivnp
                    in ( EpochConfig.toNodeId (vp-ec vpb) (vp-member vpb) ≡ pid')
                       × ∃[ v ] ( v ^∙ vEpoch < e
                                × v ^∙ vRound ≤ (₋epEC pst) ^∙ epLastVotedRound
                                × Σ (WithVerSig pk v)
                                    λ vsig → (ver-signature vsig ≡ ₋vSignature v'))

  postulate -- TODO-2: prove

    -- Given a PK

    isValidNewPart⇒fSE : ∀ {e e' pk v'}{pre : SystemState e} {post : SystemState e'} {theStep : Step pre post}
                     → IsValidNewPart (₋vSignature v') pk theStep
                     → firstSendEstablishes v' pk theStep

    -- We will use impl-sps-avp to establish the first conjunct of firstsendestablishes; it no
    -- longer needs to know its pre-state is reachable, which is inconvenient to know here.

    fSE⇒rnd≤lvr : ∀ {e e' e'' v' pk}{pre : SystemState e} {post : SystemState e'}{final : SystemState e''} {theStep : Step pre post}
                → firstSendEstablishes v' pk theStep
                → Step* post final
                → Σ (ValidPartForPK (availEpochs final) v' pk)
                    λ vpf → Σ (Is-just (Map-lookup (EpochConfig.toNodeId (vp-ec vpf) (vp-member vpf)) (peerStates final)))
                            λ ij → v' ^∙ vRound ≤ (₋epEC (to-witness ij)) ^∙ epLastVotedRound

  vo₁-unwind2 : VO.ImplObligation₁
  -- Initialization doesn't send any messages at all so far.  In future it may send messages, but
  -- probably not containing Votes?
  vo₁-unwind2 r (step-init _ eff) _ _ m∈outs _ _ _ _ _ _ _ _ rewrite cong proj₂ eff = ⊥-elim (¬Any[] m∈outs)
  vo₁-unwind2 {e} {pk = pk} {pre = pre} r sm@(step-msg {s = ps} {s' = ps'} _ ps≡ _) {v' = v'} hpk v⊂m m∈outs sig ¬sentb4 (vpb , pid≡) v'⊂m' m'∈pool sig' eIds≡ rnds≡
     -- Use unwind to find the step that first sent the signature for v', then Any-Step-elim to
     -- prove that going from the post state of that step to pre results in a state in which the
     -- round of v' is at most the last voted round recorded in the peerState of pid (the peer that
     -- sent v')
     with Any-Step-elim (fSE⇒rnd≤lvr {v' = v'} {pk})
                        (Any-Step-⇒ (λ _ ivnp → isValidNewPart⇒fSE ivnp)
                                    (unwind r hpk v'⊂m' m'∈pool sig'))
  ...| vpf' , ij , v'rnd≤lvr
     -- The fake/trivial handler always sends a vote for its current epoch, but for a
     -- round greater than its last voted round
     with newVoteSameEpochGreaterRound {e} {availEpochs pre} sm ps≡ v⊂m m∈outs sig ¬sentb4
  ...| eIds≡' , suclvr≡v'rnd , _
     -- Both votes have the same epochID, therefore same EpochConfig
     with sameEpoch⇒sameEC vpb vpf' eIds≡
  ...| refl
     -- Because the votes have the same EpochConfig and same PK, they are by
     -- the same member
     with toℕ-injective (sameEC⇒sameMember vpb vpf' refl)
  ...| refl
     -- Therefore they are by the same peer
     with trans (sym pid≡) ((cong (EpochConfig.toNodeId (vp-ec vpb)) refl))
  ...| refl
     -- So the peerState the sender of v' is the same as the peerState of the peer taking this step
     with just-injective (trans (sym ps≡) (to-witness-lemma ij refl))
     -- Now we can establish a contradiction with the hypothesis that the rounds of v and v' are equal
  -- TODO-1: this may be overly complicated now that rnd≡ is an equality
  ...| refl rewrite rnds≡ = ⊥-elim (<⇒≢ (≤-reflexive suclvr≡v'rnd) (≤-antisym (<⇒≤ (≤-reflexive suclvr≡v'rnd)) v'rnd≤lvr))

--   postulate  -- TODO : prove
--     vo₂ : VO.ImplObligation₂
