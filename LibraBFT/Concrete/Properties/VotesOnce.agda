{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Impl.Base.Types

open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle sha256 sha256-cr
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Concrete.System
open        EpochConfig
open import LibraBFT.Yasm.Yasm ℓ-EventProcessorAndMeta ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

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

 ImplObligation₁ : Set (ℓ+1 ℓ-EventProcessorAndMeta)
 ImplObligation₁ =
   ∀{pid pid' inits' s' outs pk}{pre : SystemState}
   → ReachableSystemState pre
   -- For any honest call to /handle/ or /init/,
   → StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) inits' (s' , outs)
   → ∀{v m v' m'} → Meta-Honest-PK pk
   -- For signed every vote v of every outputted message
   → v  ⊂Msg m  → m ∈ outs → (sig : WithVerSig pk v)
   -- If v is really new and valid
     -- Note that this does not directly exclude possibility of previous message with
     -- same signature, but sent by someone else.  We could prove it implies it though.
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre)) → ValidSenderForPK (availEpochs pre) v pid pk
   -- And if there exists another v' that has been sent before
   → v' ⊂Msg m' → (pid' , m') ∈ (msgPool pre) → WithVerSig pk v'
   -- If v and v' share the same epoch and round
   → (v ^∙ vEpoch) ≡ (v' ^∙ vEpoch)
   → (v ^∙ vProposed ∙ biRound) ≡ (v' ^∙ vProposed ∙ biRound)
   ----------------------------------------------------------
   -- Then an honest implemenation promises v and v' vote for the same blockId.
   → (v ^∙ vProposed ∙ biId) ≡ (v' ^∙ vProposed ∙ biId)

 ImplObligation₂ : Set (ℓ+1 ℓ-EventProcessorAndMeta)
 ImplObligation₂ =
   ∀{pid inits' s' outs pk}{pre : SystemState}
   → ReachableSystemState pre
   -- For any honest call to /handle/ or /init/,
   → StepPeerState pid (msgPool pre) (initialised pre) (peerStates pre pid) inits' (s' , outs)
   → ∀{v m v' m'} → Meta-Honest-PK pk
   -- For every vote v represented in a message output by the call
   → v  ⊂Msg m  → m ∈ outs → (sig : WithVerSig pk v)
   -- If v is really new and valid
   → ¬ (MsgWithSig∈ pk (ver-signature sig) (msgPool pre)) → ValidSenderForPK (availEpochs pre) v pid pk

   -- And if there exists another v' that is also new and valid
   → v' ⊂Msg m'  → m' ∈ outs → (sig' : WithVerSig pk v')
   → ¬ (MsgWithSig∈ pk (ver-signature sig') (msgPool pre)) → ValidSenderForPK (availEpochs pre) v' pid pk

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
  module _ (st : SystemState)(r : ReachableSystemState st)(𝓔 : EpochConfig) where

   open Structural sps-corr
   -- Bring in IntSystemState
   open WithSPS sps-corr
   open PerState st r
   open PerEpoch 𝓔

   open import LibraBFT.Concrete.Obligations.VotesOnce 𝓔 (ConcreteVoteEvidence 𝓔) as VO

   -- The VO proof is done by induction on the execution trace leading to 'st'. In
   -- Agda, this is 'r : RechableSystemState st' above.

   private

    -- From this point onwards, it might be easier to read this proof starting at 'voo'
    -- at the end of the file. Next, we provide an overview the proof.
    --
    -- We wish to prove that, for any two votes v and v' cast by an honest α in the message
    -- pool of a state st, if v and v' have equal rounds and epochs, then they vote for the
    -- same block.
    --
    -- The base case and the case for a new epoch in the system are trivial. For the base case
    -- we get to a contradiction because it's not possible to have any message in the msgpool.
    --
    -- Regarding the PeerStep case. The induction hypothesis tells us that the property holds
    -- in the pre-state.  Next, we reason about the post-state.  We start by analyzing whether
    -- v and v' have been sent as outputs of the PeerStep under scrutiny or were already in
    -- the pool before.
    --
    -- There are four possibilities:
    --
    --   i) v and v' were aleady present in the msgPool before: use induction hypothesis.
    --  ii) v and v' are both in the output produced by the PeerStep under scrutiny.
    -- iii) v was present before, but v' is new.
    --  iv) v' was present before, but v is new.
    --
    -- In order to obtain this four possiblities we invoke newMsg⊎msgSent4 lemma, which
    -- receives proof that some vote is in a message that is in the msgPool of the post state
    -- and returns evidence that either the vote is new or that some message with the same
    -- signature was sent before.
    --
    -- Case (i) is trivial; cases (iii) and (iv) are symmetric and reduce to an implementation
    -- obligation (Impl-VO1) and case (ii) reduces to a different implementation obligation
    -- (Impl-VO2).


    VotesOnceProof :
       ∀ {v v' pk} {st : SystemState}
       → ReachableSystemState st
       → Meta-Honest-PK pk
       → (vv  : WithVerSig pk v)  → MsgWithSig∈ pk (ver-signature vv) (msgPool st)
       → (vv' : WithVerSig pk v') → MsgWithSig∈ pk (ver-signature vv') (msgPool st)
       → v ^∙ vEpoch ≡ v' ^∙ vEpoch
       → v ^∙ vRound ≡ v' ^∙ vRound
       → v ^∙ vProposedId ≡ v' ^∙ vProposedId
    VotesOnceProof step-0 _ _ msv _ _ _ _ = ⊥-elim (¬Any[] (msg∈pool msv))
    VotesOnceProof (step-s r (step-peer cheat@(step-cheat f c))) pkH vv msv vv' msv' ep≡ r≡
       with ¬cheatForgeNew cheat refl unit pkH msv | ¬cheatForgeNew cheat refl unit pkH msv'
    ...| msb4 | m'sb4
       with  msgSameSig msb4 | msgSameSig m'sb4
    ...| refl | refl = VotesOnceProof r pkH vv msb4 vv' m'sb4 ep≡ r≡
    VotesOnceProof (step-s r (step-peer stHon@(step-honest stPeer))) pkH vv msv vv' msv' ep≡ r≡
       with  msgSameSig msv | msgSameSig msv'
    ...| refl       | refl
       with sameHonestSig⇒sameVoteData pkH (msgSigned msv) vv (msgSameSig msv)
          | sameHonestSig⇒sameVoteData pkH (msgSigned msv') vv' (msgSameSig msv')
    ...| inj₁ hb    | _         = ⊥-elim (meta-sha256-cr hb)
    ...| inj₂ refl  | inj₁ hb   = ⊥-elim (meta-sha256-cr hb)
    ...| inj₂ refl  | inj₂ refl
       with newMsg⊎msgSentB4 r stHon pkH (msgSigned msv) (msg⊆ msv) (msg∈pool msv)
          | newMsg⊎msgSentB4 r stHon pkH (msgSigned msv') (msg⊆ msv') (msg∈pool msv')
    ...| inj₂ msb4                   | inj₂ m'sb4
         = VotesOnceProof r pkH vv msb4 vv' m'sb4 ep≡ r≡
    ...| inj₁ (m∈outs , vspk , newV) | inj₁ (m'∈outs , v'spk , newV')
      = Impl-VO2 r stPeer pkH (msg⊆ msv) m∈outs (msgSigned msv) newV vspk
                 (msg⊆ msv') m'∈outs (msgSigned msv') newV' v'spk ep≡ r≡
    ...| inj₁ (m∈outs , vspk , newV) | inj₂ m'sb4
       with sameHonestSig⇒sameVoteData pkH (msgSigned m'sb4) vv' (msgSameSig m'sb4)
    ...| inj₁ hb   = ⊥-elim (meta-sha256-cr hb)
    ...| inj₂ refl
      = Impl-VO1 r stPeer pkH (msg⊆ msv) m∈outs (msgSigned msv) newV vspk
                 (msg⊆ m'sb4) (msg∈pool m'sb4) (msgSigned m'sb4) ep≡ r≡
    VotesOnceProof (step-s r (step-peer (step-honest stPeer))) pkH vv msv vv' msv' ep≡ r≡
       | refl       | refl
       | inj₂ refl  | inj₂ refl
       | inj₂ msb4                   | inj₁ (m'∈outs , v'spk , newV')
       with sameHonestSig⇒sameVoteData pkH (msgSigned msb4) vv (msgSameSig msb4)
    ...| inj₁ hb = ⊥-elim (meta-sha256-cr hb)
    ...| inj₂ refl
      = sym (Impl-VO1 r stPeer pkH (msg⊆ msv') m'∈outs (msgSigned msv') newV' v'spk
                      (msg⊆ msb4) (msg∈pool msb4) (msgSigned msb4) (sym ep≡) (sym r≡))

   voo : VO.Type IntSystemState
   voo hpk refl sv refl sv' round≡
      with vmsg≈v (vmFor sv) | vmsg≈v (vmFor sv')
   ...| refl | refl
       = let ver = vmsgSigned (vmFor sv)
             mswsv = mkMsgWithSig∈ (nm (vmFor sv)) (cv (vmFor sv)) (cv∈nm (vmFor sv))
                                    _ (nmSentByAuth sv) (vmsgSigned (vmFor sv)) refl
             ver' = vmsgSigned (vmFor sv')
             mswsv' = mkMsgWithSig∈ (nm (vmFor sv')) (cv (vmFor sv')) (cv∈nm (vmFor sv'))
                                     _ (nmSentByAuth sv') (vmsgSigned (vmFor sv')) refl
             epoch≡ = trans (vmsgEpoch (vmFor sv)) (sym (vmsgEpoch (vmFor sv')))
         in VotesOnceProof r hpk ver mswsv ver' mswsv' epoch≡ round≡
