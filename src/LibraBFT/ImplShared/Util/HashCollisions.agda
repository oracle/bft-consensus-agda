{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Crypto
open import Optics.All
open import Util.ByteString
open import Util.PKCS
open import Util.Prelude
open import Yasm.Base
open import Yasm.System ℓ-RoundManager ℓ-VSFP ConcSysParms

-- This module contains the machinery we use for tracking hash collisions for the hash function
-- postulated in LibraBFT.ImplShared.Util.Crypto.  (Note that, although we call it sha256 to remind
-- ourselves that this *represents* a real hash function, in fact it is just postulated and could
-- represent any hash function.)  We prove our correctness conditions modulo hash collisions of this
-- function, which is used to derive IDs for Blocks.  Therefore, how we model and reason about such
-- collisions is critical to the validity of our proofs.
--
-- A common approach is to simply assume (e.g., postulate or state as an axiom) that the function is
-- injective.  While this is a reasonable pragmatic approach, it does raise an important issue.
-- Because practical hash functions have unbounded domains and finite codomains, they are not
-- injective.  Therefore, assuming that the function represented by the postulated one is injective
-- amounts to making an unsatisfiable assumption, from which anything can be proved (false implies
-- anything).  For this reason, it is not sufficient to show that the desired property holds unless
-- a hash collision *exists*.  Instead, we must construct evidence of a *specific* hash collision
-- (i.e., two values and evidence that their hashes are the same but the values themselves are
-- different).  Such evidence is captured by the type NonInjective-≡ sha256.  Below we elaborate on
-- some subtleties and tradeoffs with what we prove in which contexts.
--
-- First, when we are dealing with *abstract* Records (as in the Abstract and Concrete modules), it
-- is trivial to construct an injectivity failure of Block IDs, simply by constructing two different
-- abstract Blocks that have the same ID.  In that context, it is important that we prove our
-- correctness conditions modulo injectivity failures between Blocks that are actually represented
-- in the specific ReachableSystemState about which we're reasoning (because that allows the
-- injectivity failure of IDs of the *abstract* Blocks to be related back to concrete blocks whose
-- IDs are derived using the hash function).
--
-- In contrast, it is far from trivial to construct a specific collision for the *postulated*
-- sha256-cr function.  It would be possible to prove that *some* collision *exists* by using a
-- pigeonhole principle counting argument.  In principle, one could then construct a specific
-- collision by generating 2 ^ 256 + 1 distinct Records (in case the postulated hash function is
-- assumed to produce 256-bit hashes), and asking for each pair of them whether they hash to the
-- same value.  We could eliminate the possibility that none of these pairs provides a collision
-- using the counting argument.
--
-- One could not do this "accidentally" (as could potentially occur with Abstract records), and
-- furthermore, by examining all proofs that use meta-no-collision, it is not difficult to see that
-- the specific collisions are all produced from Records introduced by the proof obligations (i.e.,
-- Records that are in the ReachableSystemState under consideration).  Therefore, we do not consider
-- it necessary to explicitly associate any collisions for the postulated hash function with the
-- ReachableSystemState.
--
-- Having received feedback from some people who were uncomfortable with this argument, we have put
-- some effort into explicitly tying each collision to data "in the system" in the
-- ReachableSystemState in question.  Our exploration convinces us that it's possible, but
-- reinforces our view that it is not worthwhile; we elaborate on this in comments below.
--
-- Our current position is to keep for illustrative purposes our work so far on explicitly tying
-- some hash collisions to particular Records in the system for some cases, but to continue to
-- simply construct the evidence of the collision in other cases.  The two approaches can coexist
-- because proofs can "bail out" when finding a hash collision between Records the proof is
-- considering by invoking either of the postulated functions below (meta-no-collision-in-sys and
-- meta-no-collsion).  Both state that there is no collision, so providing evidence of a specific
-- collision is sufficient to bail out of the proof of a condition that might not hold in case of a
-- collision.  The first requires the specific elements contributing to the collision to be
-- precisely located within the current ReachableSystemState, while the second requires only
-- evidence of the collision's existence, without specific information about where its elements came
-- from.  Below we explain our initial approach for meta-no-collision-in-sys, overview some examples
-- demonstrating the additional proof burden it creates, and also discuss what would be needed to
-- complete this effort, if it were deemed worthwhile.

module LibraBFT.ImplShared.Util.HashCollisions
  (iiah  : SystemInitAndHandlers ℓ-RoundManager ConcSysParms)
  where

  open WithInitAndHandlers iiah

  -- By placing the constructs below within a module that takes a ReachableSystemState as a module
  -- parameter, we ensure that a proof that wants to "bail out" due to a hash collision must specify
  -- a ReachableSystemState and show that the specific collision is between elements represented in
  -- that state.

  module PerReachableState {st} (r : ReachableSystemState st) where

    -- The following datatypes are used in the definition of HashCollisionFound below to enumerate
    -- the ways in which hash collisions that would undermine correctness can arise in the given
    -- state st.  Note that we do not need to capture all ways in which a ByteString might be
    -- represented, only those for which our proofs require injectivity properties.  Our initial
    -- work requires capturing hash collisions only for Block IDs.

    data _∈Block_ : BSL → Block → Set where
      inB : ∀ {b} → blockData-bsl (b ^∙ bBlockData) ∈Block b
    open _∈Block_

    data _∈ProposalMsg_ (bsl : BSL) (pm : ProposalMsg) : Set where
      inPM : bsl ∈Block (pm ^∙ pmProposal) → bsl ∈ProposalMsg pm
    open _∈ProposalMsg_

    data _∈nm (bsl : BSL) : Set where
      inP : ∀ {sndr pm} → (sndr , P pm) ∈ msgPool st → bsl ∈ProposalMsg pm → bsl ∈nm
    open _∈nm

    -- We could refine this further (∈BlockTree, ∈btIdToBlock), but I don't think we need to.
    data _∈BS_ (bsl : BSL) (bs : BlockStore) : Set where
      inBS : ∀ {eb} → (getBlock (hashBSL bsl) bs ≡ just eb) → bsl ∈Block (eb ^∙ ebBlock) → bsl ∈BS bs

    data _∈RM_ (bsl : BSL) (rm : RoundManager) : Set where
      inRM : bsl ∈BS (rm ^∙ lBlockStore) → bsl ∈RM rm

    -- So far, HashCollisionFound includes two constructors, one (msgRmHC) for a collision between a
    -- ByteString represented in a message that has been sent (∈nm) and one represented in the
    -- RoundManager of some peer.  The other (msgmsgHC) is unused so far, but would be needed if we
    -- were to take this work further; it is for cases in which there is a collision between two
    -- elements in messages that have been sent.

    data HashCollisionFound : Set where
      msgRmHC  : ∀ {bs1 bs2 pid}
               → bs1 ∈nm
               → initialised st pid ≡ initd
               → bs2 ∈RM (peerStates st pid)
               → hashBSL bs1 ≡ hashBSL bs2
               → bs1 ≢ bs2
               → HashCollisionFound
      msgmsgHC : ∀ {bs1 bs2}
               → bs1 ∈nm
               → bs2 ∈nm
               → hashBSL bs1 ≡ hashBSL bs2
               → bs1 ≢ bs2
               → HashCollisionFound

    -- By postulating the lack of existence of HashCollisionFound, we enable any proof to "bail out"
    -- only if it can construct a *specific* hash collision that is "in the system" represented by
    -- the specific ReachableSystemState, according to the specific notions thereof captured by the
    -- constructors for this type.

    postulate -- Valid assumption: there are no hash collisions among values found in the system
      meta-no-collision-in-sys : ¬ HashCollisionFound

    -- Discussion
    --
    -- As noted above, we have applied this approach to some proofs but not others.  In particular,
    -- there are still a number of proofs that use meta-no-collision (below), which does not require
    -- the constructed collision to be explicitly placed in context of the ReachableSystemState.
    --
    -- We have used meta-no-collision-in-sys for the case of a peer handling a proposal.  The
    -- proposal contains a Block which has an ID, which is supposed to be the hash of some parts of
    -- the proposal.  This condition is verified when the proposal message is first received (see
    -- verifyWellFormed in LibraBFT.Impl.Consensus.ConsensusTypes.Block), and the knowledge that it
    -- verified correctly is needed all the way down the stack when the receiving peer inserts the
    -- block into its BlockTree.  If an ExecutedBlock is found in the BlockTree associated with the
    -- ID of the new Block, then the algorithm assumes it's the same Block (because both the new
    -- Block and the one inserted previously in the BlockTree have been verified as hashing to the
    -- same ID).  If there were a collision (i.e., these two Blocks that hash to the same ID
    -- actually have different bits that are hashed to derive the ID), then incorrect behaviour
    -- would be possible.
    --
    -- To use meta-no-collision-in-sys, we need to construct a value of HashCollisionFound in
    -- context of the ReachableSystemState under consideration (but see note below).  This requires
    -- carrying the fact that the hash of the newly proposed Block matches its ID from the
    -- above-mentioned verification all the way down the stack, where it is needed to invoke an
    -- assumption about the lack of collisions between the new Block and one previously stored when
    -- proving the Contract for insertBlockESpec. (This is the NOHC1 argument given to the blocks≈
    -- field insertBlockESpec.ContrackOk.)  Then, each Contract up the stack must receive a similar
    -- argument enabling it to invoke the Contract of the next function down the stack.  See, for
    -- example, the ebBlock≈ field of executeAndInsertBlockESpec.ContractOk, the voteAttemptCorrect
    -- field of processProposalMsgMSpec.Contract (and others in the same file), and similarly for
    -- handleProposalSpec.Contract.  Then this argument must be provided by higher level properties
    -- that wish to invoke the lower-level contracts.  Because the higher-level properties are in
    -- context of a specific ReachableSystemState, they can construct a proof of the absence of the
    -- potential collision by using meta-no-collision-in-sys for that ReachableSystemState.
    --
    -- As can be seen, connecting a potential hash collision to a specific ReachableSystemState is a
    -- fair amount of work, which complicates proofs.  As explained above, we do not think it is
    -- worthwhile to continue this effort, just to show that we can.  One issue we would want to
    -- address if taking this work further would be to *ensure* that the ReachableSystemState
    -- for which a potential collision is considered is the same one about which we're proving the
    -- given property.  This already is the case in our proofs, but our conditions don't *ensure*
    -- that it is because, in principle, when calling nohc to use meta-no-collision-in-sys to
    -- eliminate an assumed collision, we could provide *any* ReachableSystemState.  To require it
    -- to be the same ReachableSystemState, we would need to explicitly express for each relevant
    -- property that it holds unless there is collision in *that state*.  So, for example, the
    -- conclusion of the IncreasingRoundObligation property would have to become something like the
    -- following (where pre is the state about which IncreasingRoundObligation is proved):
    --
    --     HashCollisionFound pre
    --   ⊎ v' ^∙ vRound < v ^∙ vRound
    --   ⊎ VoteForRound∈ pk (v ^∙ vRound) (v ^∙ vEpoch) (v ^∙ vProposedId) (msgPool pre)
    --
    -- The first disjunct is not currently necessary because there is no requirement to place the
    -- HashCollisionFound in the same ReachableSystemState.  We would then need to propagate those
    -- disjuncts from one proof to another, making even more work and complicating proofs and
    -- properties further.  Importantly, doing so would provide no additional benefit over what we
    -- have done already, exactly because it is not practical to construct a collision for the
    -- postulated hash function anyway (and we could not do so "accidentally"): giving ourselves the
    -- freedom to associate it with a diffferent ReachabeSystemState does not change that.  This
    -- underlines the point that requiring the collision to be associated with a
    -- ReachableSystemState creates quite a bit of work, and provides little benefit.

    postulate  -- valid assumption.  Note that this does *not* say that no collisions *exist*; it
               -- says a proof cannot escape its obligations unless it can provide specfic evidence
               -- of a collision; as explained above, doing so other than from Records presented to
               -- the proof (because they are in the system state under consideration) is
               -- impractical and impossible to do "accidentally"
      meta-no-collision : ¬ (NonInjective-≡ sha256)

    sameSig⇒sameVoteDataNoCol : ∀ {v1 v2 : Vote} {pk}
                              → WithVerSig pk v1
                              → WithVerSig pk v2
                              → v1 ^∙ vSignature ≡ v2 ^∙ vSignature
                              → v2 ^∙ vVoteData ≡ v1 ^∙ vVoteData
    sameSig⇒sameVoteDataNoCol {v1} {v2} wvs1 wvs2 refl
       with sameSig⇒sameVoteData {v1} {v2} wvs1 wvs2 refl
    ...| inj₁ hb = ⊥-elim (meta-no-collision hb)
    ...| inj₂ x = x

