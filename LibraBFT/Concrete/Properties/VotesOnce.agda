{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS

open import LibraBFT.Abstract.Types
open EpochConfig

open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle sha256 sha256-cr

open import LibraBFT.Concrete.System.Parameters

open import LibraBFT.Yasm.Base
open import LibraBFT.Yasm.AvailableEpochs using (AvailableEpochs ; lookup'; lookup'')
open import LibraBFT.Yasm.System     ConcSysParms
open import LibraBFT.Yasm.Properties ConcSysParms

-- In this module, we define two "implementation obligations"
-- (ImplObligationᵢ for i ∈ {1 , 2}), which are predicates over
-- reachable states of a system defined by
-- 'LibraBFT.Concrete.System.Parameters'.  These two properties relate
-- votes sent by the same sender, ensuring that if they are for the
-- same epoch and round, then they vote for the same blockID; the
-- first relates a vote output by the handler to a vote sent
-- previously, and the second relates two votes both sent by the
-- handler.
--
-- We then prove that, if an implementation satisfies these two
-- semantic obligations, along with a structural one about messages
-- sent by honest peers in the implementation, then the implemenation
-- satisfies the LibraBFT.Abstract.Properties.VotesOnce invariant.
module LibraBFT.Concrete.Properties.VotesOnce where

 -- TODO-3: This may not be the best way to state the implementation obligation.  Why not reduce
 -- this as much as possible before giving the obligation to the implementation?  For example, this
 -- will still require the implementation to deal with hash collisons (v and v' could be different,
 -- but yield the same bytestring and therefore same signature).  Also, avoid the need for the
 -- implementation to reason about messages sent by step-cheat, or give it something to make this
 -- case easy to eliminate.

 ImplObligation₁ : Set
 ImplObligation₁ =
   ∀{e pid sndr s' outs pk}{pre : SystemState e}
   → ReachableSystemState pre
   -- For any honest call to /handle/ or /init/,
   → StepPeerState pid (availEpochs pre) (msgPool pre) (Map-lookup pid (peerStates pre)) s' outs
   → ∀{v m v' m'} → Meta-Honest-PK pk
   -- For signed every vote v of every outputted message
   → v  ⊂Msg m  → m ∈ outs → (sig : WithVerSig pk v)
   -- If v is really new and valid
     -- Note that this does not directly exclude possibility of previous message with
     -- same signature, but sent by someone else.  We could prove it implies it though.
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre)) → ValidPartForPK (availEpochs pre) v pk
   -- And if there exists another v' that has been sent before
   → v' ⊂Msg m' → (sndr , m') ∈ (msgPool pre) → WithVerSig pk v'
   -- If v and v' share the same epoch and round
   → (v ^∙ vEpoch) ≡ (v' ^∙ vEpoch)
   → (v ^∙ vProposed ∙ biRound) ≡ (v' ^∙ vProposed ∙ biRound)
   ----------------------------------------------------------
   -- Then an honest implemenation promises v and v' vote for the same blockId.
   → (v ^∙ vProposed ∙ biId) ≡ (v' ^∙ vProposed ∙ biId)

 ImplObligation₂ : Set
 ImplObligation₂ =
   ∀{e pid s' outs pk}{pre : SystemState e}
   → ReachableSystemState pre
   -- For any honest call to /handle/ or /init/,
   → StepPeerState pid (availEpochs pre) (msgPool pre) (Map-lookup pid (peerStates pre)) s' outs
   → ∀{v m v' m'} → Meta-Honest-PK pk
   -- For every vote v represented in a message output by the call
   → v  ⊂Msg m  → m ∈ outs → (sig : WithVerSig pk v)
   -- If v is really new and valid
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre)) → ValidPartForPK (availEpochs pre) v pk

   -- And if there exists another v' that is also new and valid
   → v' ⊂Msg m'  → m' ∈ outs → (sig' : WithVerSig pk v')
   → ¬ (MsgWithSig∈ pk (ver-signature sig') (msgPool pre)) → ValidPartForPK (availEpochs pre) v' pk

   -- If v and v' share the same epoch and round
   → (v ^∙ vEpoch) ≡ (v' ^∙ vEpoch)
   → (v ^∙ vProposed ∙ biRound) ≡ (v' ^∙ vProposed ∙ biRound)
   ----------------------------------------------------------
   -- Then, an honest implemenation promises v and v' vote for the same blockId.
   → (v ^∙ vProposed ∙ biId) ≡ (v' ^∙ vProposed ∙ biId)

 -- Next, we prove that, given the necessary obligations,
 module Proof
   (sps-corr : StepPeerState-AllValidParts)
   (Impl-VO1 : ImplObligation₁)
   (Impl-VO2 : ImplObligation₂)
   where

  -- Any reachable state satisfies the VO rule for any epoch in the system.
  module _ {e}(st : SystemState e)(r : ReachableSystemState st)(eid : Fin e) where
   -- Bring in 'unwind', 'ext-unforgeability' and friends
   open Structural sps-corr

   -- Bring in ConcSystemState
   open import LibraBFT.Concrete.System sps-corr
   open PerState st r
   open PerEpoch eid

   -- TODO-4: For now we assume 𝓔 is a "ValidEpoch", but in the future we should prove that all
   -- epochs in the system are valid. This will be dependent on how the epoch-change-transaction
   -- mechanism is architected and consequently is left as future work.
   module _ (valid-𝓔 : ValidEpoch 𝓔) where
    open import LibraBFT.Abstract.Properties 𝓔 valid-𝓔 Hash _≟Hash_ (ConcreteVoteEvidence 𝓔)

    -- The VO proof is done by induction on the execution trace leading to 'st'. In
    -- Agda, this is 'r : RechableSystemState st' above. We will use induction to
    -- construct a predicate Pred'' below, which holds for every state on the trace.

    private
     -- First we specify the predicate we need: it relates two votes verified
     -- by the same public key, such that both are elements of the same message pool
     Pred'' : PK → Vote → Vote → SentMessages → Set
     Pred'' pk v v' pool
       = Meta-Honest-PK pk
       → (ver  : WithVerSig pk v)  → MsgWithSig∈ pk (ver-signature ver) pool
       → (ver' : WithVerSig pk v') → MsgWithSig∈ pk (ver-signature ver') pool
       → v ^∙ vEpoch ≡ v' ^∙ vEpoch
       → v ^∙ vRound ≡ v' ^∙ vRound
       → v ^∙ vProposedId ≡ v' ^∙ vProposedId

     -- Usually, we want to universally quantify Pred'' over arbitrary votes and pks
     Pred' : SentMessages → Set
     Pred' pool = ∀{pk}{v v' : Vote} → Pred'' pk v v' pool

     -- Finally, we state Pred' in terms of SystemSate
     Pred : ∀{e} → SystemState e → Set
     Pred = Pred' ∘ msgPool

     -------------------
     -- * Base Case * --
     -------------------

     -- Pred above is trivially true for the initial state: there are no messages in the pool
     Pred₀ : Pred initialState
     Pred₀ _ _ ()

     --------------------------------------------------
     -- * Inductive Case: New Epochs in the System * --
     --------------------------------------------------

     -- Because pushEpoch does not alter the msgPool, the proof is trivial.
     Pred𝓔 : ∀{e}{st : SystemState e}(𝓔 : EpochConfigFor e) → Pred st → Pred (pushEpoch 𝓔 st)
     Pred𝓔 𝓔 p = p

     ----------------------------------------------
     -- * Inductive Case: Transition by a Peer * --
     ----------------------------------------------

     -- From this point onwards, it might be easier to read this proof starting at 'voo'
     -- at the end of the file. Next, we provide an overview the proof.
     --
     -- We wish to prove that, for any two votes v and v' cast by an honest α in the message pool of
     -- a state st, if v and v' have equal rounds and epochs, then they vote for the same block. As
     -- we have seen above, the base case and the case for a new epoch in the system are
     -- trivial. Next, we look at the PeerStep case.
     --
     -- The induction hypothesis tells us that the property holds in the pre-state.  Next, we reason
     -- about the post-state.  We start by analyzing whether v and v' have been sent as outputs of
     -- the PeerStep under scrutiny or were already in the pool before (captured by the PredStep
     -- function).  There are four possibilities:
     --
     --   i) v and v' were aleady present in the msgPool before: use induction hypothesis.
     --  ii) v and v' are both in the output produced by the PeerStep under scrutiny.
     -- iii) v was present before, but v' is new.
     --  iv) v' was present before, but v is new.
     --
     -- Case (i) is trivial; cases (iii) and (iv) are symmetric and reduce to an implementation
     -- obligation (Impl-VO1) and case (ii) reduces to a different implementation obligation (Impl-VO2).
     --
     -- The proofs of cases (iii) and (iv) are in PredStep-wlog-ht and PredStep-wlog-ht'.  The 'ht'
     -- suffix refers to 'Here-There' as in one vote is "here" and the other is old, or "there".  We
     -- first analyze whether the new vote is really new or a replay; sps-cor provides us this
     -- information.  If the new vote is, in fact, a replay of an old message, we have two old
     -- messages and can call the induction hypothesis. If it is really new, we must rely on the
     -- implementation obligation. But to do so, we must prove that the old vote was also sent by
     -- the same peer.  We can see that is the case by reasoning about PK-inj and IsValidEpochMember.
     --
     -- Finally, the proof of case (ii) also branches on whether either of the "new" votes
     -- are replays or are really new. In case at least one is a replay we fallback to cases (iii) and (iv)
     -- or just call the induction hypothesis when both are replays.
     -- When both votes are in fact new, we rely on Impl-VO2 to conclude.
     --
     -- In both PredSetp-wlog-ht and PredStep-wlog-hh, we must eliminate the possibility of
     -- either vote being produced by a cheat step. This is easy because we received
     -- a proof that the PK in question is honest, hence, it must be the case that a cheat
     -- step is at most replaying these votes, not producing them. Producing them would
     -- require the cheater to forge a signature. This is the purpose of the isCheat constraint.

     PredStep-wlog-ht' : ∀{e pid pid' s' outs pk}{pre : SystemState e}
             → ReachableSystemState pre
             → Pred pre
             → StepPeerState pid (availEpochs pre) (msgPool pre) (Map-lookup pid (peerStates pre)) s' outs
             → ∀{v m v' m'}
             → v  ⊂Msg m  → m ∈ outs
             → v' ⊂Msg m' → (pid' , m') ∈ msgPool pre
             → WithVerSig pk v → WithVerSig pk v' → Meta-Honest-PK pk
             → (v ^∙ vEpoch) ≡ (v' ^∙ vEpoch)
             → (v ^∙ vProposed ∙ biRound) ≡ (v' ^∙ vProposed ∙ biRound)
             → (v ^∙ vProposed ∙ biId) ≡ (v' ^∙ vProposed ∙ biId)
     PredStep-wlog-ht' {pre = pre} preach hip ps {v} v⊂m m∈outs v'⊂m' m'∈pool ver ver' hpk eids≡ r≡
     -- (1) The first step is branching on whether 'v' above is a /new/ vote or not.
     -- (1.1) If it's new:
       with sps-corr preach hpk ps m∈outs v⊂m ver
     ...| inj₁ (vValid , vNew)
       with honestPartValid preach hpk v'⊂m' m'∈pool ver'
     ...| v'Old , vOldValid
       with sameHonestSig⇒sameVoteData hpk ver' (msgSigned v'Old) (sym (msgSameSig v'Old))
     ...| inj₁ abs  = ⊥-elim (meta-sha256-cr abs)
     ...| inj₂ refl = Impl-VO1 preach ps hpk v⊂m m∈outs ver vNew vValid
                        (msg⊆ v'Old) (msg∈pool v'Old)
                        (msgSigned v'Old) eids≡ r≡
     -- (1.1) If 'v' is not new, then there exists a msg sent with the
     -- same signature.
     PredStep-wlog-ht' preach hip ps {v} v⊂m m∈outs v'⊂m' m'∈pool ver ver' hpk e≡ r≡
        | inj₂ vOld
       with honestPartValid preach hpk v'⊂m' m'∈pool ver'
     ...| sv' , _ = hip hpk ver vOld ver' sv' e≡ r≡

     -- Here we prove a modified version of Pred'' where we assume w.l.o.g that
     -- one vote is sent by "pstep" and another was present in the prestate.
     PredStep-wlog-ht
       : ∀{e pid st' outs}{pre : SystemState e}
       → ReachableSystemState pre
       → (pstep : StepPeer pre pid st' outs)
       → Pred pre
       → ∀{pk v v'}
       -- Below is a inline expansion of "Pred'' pk v v' (msgPool (StepPeer-post pstep))",
       -- but with the added information that one vote (v) was sent by pstep whereas the
       -- other (v') was in the pool of the prestate.
       → let pool = msgPool (StepPeer-post pstep)
          in Meta-Honest-PK pk
           → (ver  : WithVerSig pk v )(sv  : MsgWithSig∈ pk (ver-signature ver ) pool)
           → (msgSender sv , msgWhole sv) ∈ List-map (pid ,_) outs
           → (ver' : WithVerSig pk v')(sv' : MsgWithSig∈ pk (ver-signature ver') pool)
           → (msgSender sv' , msgWhole sv') ∈ msgPool pre
           → v ^∙ vEpoch ≡ v' ^∙ vEpoch
           → v ^∙ vRound ≡ v' ^∙ vRound
           → v ^∙ vProposedId ≡ v' ^∙ vProposedId
     PredStep-wlog-ht preach (step-cheat fm isCheat) hip hpk ver sv (here refl) ver' sv' furtherBack' epoch≡ r≡
       with isCheat (msg⊆ sv) (msgSigned sv)
     ...| inj₁ abs    = ⊥-elim (hpk abs) -- The key was honest by hypothesis.
     ...| inj₂ sentb4
        -- the cheater replayed the message; which means the message was sent before this
        -- step; hence, call induction hypothesis.
       with msgSameSig sv
     ...| refl = hip hpk ver sentb4 ver' (MsgWithSig∈-transp sv' furtherBack') epoch≡ r≡
     PredStep-wlog-ht preach (step-honest x) hip hpk ver sv thisStep ver' sv' furtherBack' epoch≡ r≡
       with sameHonestSig⇒sameVoteData hpk ver (msgSigned sv) (sym (msgSameSig sv))
     ...| inj₁ abs  = ⊥-elim (meta-sha256-cr abs)
     ...| inj₂ refl
       with sameHonestSig⇒sameVoteData hpk ver' (msgSigned sv') (sym (msgSameSig sv'))
     ...| inj₁ abs  = ⊥-elim (meta-sha256-cr abs)
     ...| inj₂ refl
        = PredStep-wlog-ht' preach hip x
                  (msg⊆ sv) (Any-map (cong proj₂) (Any-map⁻ thisStep))
                  (msg⊆ sv') furtherBack'
                  (msgSigned sv) (msgSigned sv') hpk epoch≡ r≡

     -- Analogous to PredStep-wlog-ht', but here we must reason about two messages that are in the
     -- outputs of a step.
     PredStep-hh' : ∀{e pid s' outs pk}{pre : SystemState e}
             → ReachableSystemState pre → Pred pre
             → StepPeerState pid (availEpochs pre) (msgPool pre) (Map-lookup pid (peerStates pre)) s' outs
             → ∀{v m v' m'}
             → v  ⊂Msg m  → m  ∈ outs
             → v' ⊂Msg m' → m' ∈ outs
             → WithVerSig pk v → WithVerSig pk v' → Meta-Honest-PK pk
             → (v ^∙ vEpoch) ≡ (v' ^∙ vEpoch)
             → (v ^∙ vProposed ∙ biRound) ≡ (v' ^∙ vProposed ∙ biRound)
             → (v ^∙ vProposed ∙ biId) ≡ (v' ^∙ vProposed ∙ biId)
     -- Since the step is from an honest peer, we can check whether the messages are in fact
     -- new or not.
     PredStep-hh' preach hip ps {v} v⊂m m∈outs v'⊂m' m'∈outs ver ver' hpk e≡ r≡
       with sps-corr preach hpk ps m∈outs v⊂m ver | sps-corr preach hpk ps m'∈outs v'⊂m' ver'
     -- (A) Both are old: call induction hypothesis
     ...| inj₂ vOld            | inj₂ v'Old = hip hpk ver vOld ver' v'Old e≡ r≡

     -- (B) One is new, one is old: use PredStep-wlog-ht'
     PredStep-hh' preach hip ps {v} v⊂m m∈outs v'⊂m' m'∈outs ver ver' hpk e≡ r≡
        | inj₁ (vValid , vNew) | inj₂ v'Old
       with sameHonestSig⇒sameVoteData hpk ver' (msgSigned v'Old) (sym (msgSameSig v'Old))
     ...| inj₁ abs  = ⊥-elim (meta-sha256-cr abs)
     ...| inj₂ refl
        = PredStep-wlog-ht' preach hip ps v⊂m m∈outs (msg⊆ v'Old) (msg∈pool v'Old) ver (msgSigned v'Old) hpk e≡ r≡

     -- (C) One is old, one is new: use PredStep-wlog-ht'
     PredStep-hh' preach hip ps {v} v⊂m m∈outs v'⊂m' m'∈outs ver ver' hpk e≡ r≡
        | inj₂ vOld            | inj₁ (v'Valid , v'New)
       with sameHonestSig⇒sameVoteData hpk ver (msgSigned vOld) (sym (msgSameSig vOld))
     ...| inj₁ abs  = ⊥-elim (meta-sha256-cr abs)
     ...| inj₂ refl
        = sym (PredStep-wlog-ht' preach hip ps v'⊂m' m'∈outs (msg⊆ vOld) (msg∈pool vOld) ver' (msgSigned vOld) hpk (sym e≡) (sym r≡))

     -- (D) Finally, both votes are new in this step. The proof is then trivially
     -- forwarded to the implementation obligation.
     PredStep-hh' preach hip ps {v} v⊂m m∈outs v'⊂m' m'∈outs ver ver' hpk e≡ r≡
        | inj₁ (vValid , vNew) | inj₁ (v'Valid , v'New)
        = Impl-VO2 preach ps hpk v⊂m m∈outs ver vNew vValid v'⊂m' m'∈outs ver' v'New v'Valid e≡ r≡

     PredStep-hh
       : ∀{e pid st' outs}{pre : SystemState e}
       → ReachableSystemState pre
       → (pstep : StepPeer pre pid st' outs)
       → Pred pre
       → ∀{pk v v'}
       → let pool = msgPool (StepPeer-post pstep)
          in Meta-Honest-PK pk
           → (ver  : WithVerSig pk v )(sv  : MsgWithSig∈ pk (ver-signature ver ) pool)
           → (msgSender sv  , msgWhole sv)  ∈ List-map (pid ,_) outs
           → (ver' : WithVerSig pk v')(sv' : MsgWithSig∈ pk (ver-signature ver') pool)
           → (msgSender sv' , msgWhole sv') ∈ List-map (pid ,_) outs
           → v ^∙ vEpoch ≡ v' ^∙ vEpoch
           → v ^∙ vRound ≡ v' ^∙ vRound
           → v ^∙ vProposedId ≡ v' ^∙ vProposedId
     PredStep-hh preach (step-cheat fm isCheat) hip hpk ver sv (here refl) ver' sv' (here refl) epoch≡ r≡
       with isCheat (msg⊆ sv) (msgSigned sv)
     ...| inj₁ abs    = ⊥-elim (hpk abs) -- The key was honest by hypothesis.
     ...| inj₂ sentb4
       with isCheat (msg⊆ sv') (msgSigned sv')
     ...| inj₁ abs     = ⊥-elim (hpk abs) -- The key was honest by hypothesis.
     ...| inj₂ sentb4'
       with msgSameSig sv | msgSameSig sv'
     ...| refl | refl = hip hpk ver sentb4 ver' sentb4' epoch≡ r≡
     PredStep-hh preach (step-honest x) hip hpk ver sv thisStep ver' sv' thisStep' epoch≡ r≡
       with sameHonestSig⇒sameVoteData hpk ver (msgSigned sv) (sym (msgSameSig sv))
     ...| inj₁ abs  = ⊥-elim (meta-sha256-cr abs)
     ...| inj₂ refl
       with sameHonestSig⇒sameVoteData hpk ver' (msgSigned sv') (sym (msgSameSig sv'))
     ...| inj₁ abs  = ⊥-elim (meta-sha256-cr abs)
     ...| inj₂ refl
        = PredStep-hh' preach hip x
                  (msg⊆ sv ) (Any-map (cong proj₂) (Any-map⁻ thisStep))
                  (msg⊆ sv') (Any-map (cong proj₂) (Any-map⁻ thisStep'))
                  (msgSigned sv) (msgSigned sv') hpk epoch≡ r≡


     PredStep : ∀{e pid st' outs}{pre : SystemState e}
              → ReachableSystemState pre
              → (pstep : StepPeer pre pid st' outs)
              → Pred pre
              → Pred (StepPeer-post pstep)
     PredStep {e} {pid} {st'} {outs} {pre} preach pstep hip hpk ver sv ver' sv' epoch≡ r≡
     -- First we check when have the votes been sent:
       with Any-++⁻ (List-map (pid ,_) outs) {msgPool pre} (msg∈pool sv)
          | Any-++⁻ (List-map (pid ,_) outs) {msgPool pre} (msg∈pool sv')
     -- (A) Neither vote has been sent by the step under scrutiny: invoke inductive hypothesis
     ...| inj₂ furtherBack | inj₂ furtherBack'
        = hip hpk ver  (MsgWithSig∈-transp sv furtherBack)
                  ver' (MsgWithSig∈-transp sv' furtherBack') epoch≡ r≡
     -- (B) One vote was cast here; the other was cast in the past.
     PredStep {e} {pid} {st'} {outs} {pre} preach pstep hip hpk ver sv ver' sv' epoch≡ r≡
        | inj₁ thisStep    | inj₂ furtherBack'
        = PredStep-wlog-ht preach pstep hip hpk ver sv thisStep ver' sv' furtherBack' epoch≡ r≡
     -- (C) Symmetric to (B)
     PredStep {e} {pid} {st'} {outs} {pre} preach pstep hip hpk ver sv ver' sv' epoch≡ r≡
        | inj₂ furtherBack | inj₁ thisStep'
        = sym (PredStep-wlog-ht preach pstep hip hpk ver' sv' thisStep' ver sv furtherBack (sym epoch≡) (sym r≡))
     -- (D) Both votes were cast here
     PredStep {e} {pid} {st'} {outs} {pre} preach pstep hip hpk ver sv ver' sv' epoch≡ r≡
        | inj₁ thisStep    | inj₁ thisStep'
        = PredStep-hh preach pstep hip hpk ver sv thisStep ver' sv' thisStep' epoch≡ r≡

    voo : VotesOnce.Type ConcSystemState
    voo hpk refl sv refl sv' round≡
      with Step*-Step-fold Pred (λ {e} {st} _ → Pred𝓔 {e} {st}) PredStep Pred₀ r
    ...| res
      with vmsg≈v (vmFor sv) | vmsg≈v (vmFor sv')
    ...| refl | refl
       = res hpk (vmsgSigned (vmFor sv))
                 (mkMsgWithSig∈ (nm (vmFor sv)) (cv (vmFor sv)) (cv∈nm (vmFor sv))
                                _ (nmSentByAuth sv) (vmsgSigned (vmFor sv)) refl)
                 (vmsgSigned (vmFor sv'))
                 (mkMsgWithSig∈ (nm (vmFor sv')) (cv (vmFor sv')) (cv∈nm (vmFor sv'))
                                _ (nmSentByAuth sv') (vmsgSigned (vmFor sv')) refl)
                 (trans (vmsgEpoch (vmFor sv)) (sym (vmsgEpoch (vmFor sv'))))
                 round≡
