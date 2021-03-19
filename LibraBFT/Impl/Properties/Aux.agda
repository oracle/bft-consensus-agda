{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.Obligations
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.NetworkMsg
open import LibraBFT.Impl.Util.Crypto
open        EpochConfig
open import LibraBFT.Yasm.Yasm (ℓ+1 0ℓ) EpochConfig epochId authorsN ConcSysParms NodeId-PK-OK

-- In this module, we will prove a structural property that any new signed message produced by an
-- honest handler from a reachable state correctly identifies the sender, and is for a valid epoch
-- of which that sender is a member.  It is postulated for now, because the property does not yet
-- hold for our fake implementation that does not actually comply.  A proof outline and notes are
-- included below, which we can finish once we do have a compliant implementation.

module LibraBFT.Impl.Properties.Aux where
  -- This proof is complete except for pieces that are directly about the handlers.  Our
  -- fake/simple handler does not yet obey the needed properties, so we can't finish this yet.
  impl-sps-avp : StepPeerState-AllValidParts
  -- In our fake/simple implementation, init and handling V and C msgs do not send any messages
  impl-sps-avp _ hpk (step-init ix eff) m∈outs part⊂m ver        rewrite (cong proj₂ eff) = ⊥-elim (¬Any[] m∈outs)
  impl-sps-avp _ hpk (step-msg {sndr , V vm} _ _ eff) m∈outs _ _ rewrite (cong proj₂ eff) = ⊥-elim (¬Any[] m∈outs)
  impl-sps-avp _ hpk (step-msg {sndr , C cm} _ _ eff) m∈outs _ _ rewrite (cong proj₂ eff) = ⊥-elim (¬Any[] m∈outs)
  -- These aren't true yet, because processProposalMsgM sends fake votes that don't follow the rules for ValidPartForPK
  impl-sps-avp preach hpk (step-msg {sndr , P pm} m∈pool ps≡ eff) m∈outs v⊂m ver
     with m∈outs
     -- Handler sends at most one vote, so it can't be "there"
  ...| there {xs = xs} imp rewrite proj₂ (∷-injective (cong proj₂ eff)) = ⊥-elim (¬Any[] imp)
  ...| here refl rewrite proj₁ (∷-injective (cong proj₂ eff))
     with v⊂m
  ...| vote∈qc vs∈qc rbld≈ qc∈m
     with qc∈m
  ...| withVoteSIHighQC x = {!x!} -- We will prove that votes represented in the SyncInfo of a
                                  -- proposal message were sent before, so these will both be inj₂.
                                  -- This will be based on an invariant of the implementation, for
                                  -- example that the QCs included in the SyncInfo of a VoteMsg have
                                  -- been sent before.  We will need to use hash injectivity and
                                  -- signature injectivity to ensure a different vote was not sent
                                  -- previously with the same signature.
  ...| withVoteSIHighCC x = {!!}

  impl-sps-avp {pk = pk} {α = α} {st = st} preach hpk (step-msg {sndr , P pm} m∈pool ps≡ eff) m∈outs v⊂m ver
     | here refl
     | vote∈vm {si}
     with MsgWithSig∈? {pk} {ver-signature ver} {msgPool st}
  ...| yes msg∈ = inj₂ msg∈
  ...| no  msg∉ = inj₁ ((mkValidSenderForPK      {! epoch !} -- We will need an invariant that says the epoch
                                                             -- used by a voter is "in range".
                                                 (EC-lookup' (availEpochs st) {!!})
                                                 refl
                                                 {! !}       -- The implementation will need to check that the voter is a member of
                                                             -- the epoch of the message it's sending.
                                                 )
                        , msg∉)
