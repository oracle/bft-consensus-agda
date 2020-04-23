open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import Optics.All

-- Here are the invariants that we expect the handle function
-- to satisfy.
module LibraBFT.Global.Invariants 
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  open import LibraBFT.Concrete.Consensus.Types.EpochIndep
  open import LibraBFT.Concrete.NetworkMsg

  -- instead of postulating the whole system layer here, I'll
  -- just have a self-descriptive predicate. We can struggle to
  -- define this based on the system layer later.
  postulate 
    HasBeenSent : NetworkMsg → Set


-- VCM: I'm trying to understand how to sketch the proof that our implementation
-- will (hopefully! :) ) satisfy the abstract invariants. This has
-- been refactored to Global.BlockTreeInvariants because we need knowledge of
-- the all-knowing all-seeing system's layer.
-- 
-- Recalling my comment from Concrete.BlockTreeAbstraction:849, it is inline
-- with what Mark has been thinking.
-- 
--  -- TODO: Our algorithm will ensure we never cast a vote to a proposal
--  -- that references a round smaller than our previous round. We will need
--  -- a proof of that. Moreover, we'll later need someway to lift properties
--  -- from our own algorithm to another honest author... I need to think carefully
--  -- about this.
-- 
-- That is, we need a way to say "α follows the same algo because α is honest, hence,
-- the invariants apply to α"
--
-- I like Mark's idea of saying something in the lines of:
-- If I have a record in my state with a verified signature but I'm not
-- the author, then this must have been sent by someone.
--
-- r ∈ myState → WithVerSig r → author r ≢ me → ∃[msg] (msgRecord ≡ r ∧ HasBeenSent msg)
--
-- As we can see, however, there is a disconnect from records and messages.
-- Looking at the QuorumCertificate datatype, how do we make a WithVerSig Vote
-- from the list of votes? I have no idea!
-- We might have to keep the received messages and a proof that we checked
-- their signatures somewhere; I suspect that we might be able to pull this off
-- keepnig a proof that each vote in a QC has a WithVerSig in Consensus.Types.IsValidQC
--
-- Let's leave this problem for the future and move on, though.
--
-- The idea, taken from mark-property-musings, is that we will be able to
-- prove the invariants because honest peers also respect them, hence, when
-- we saw votes from α, they must have been sent by α, who runs the Concrete.Handle.handle,
-- Hence, properties about Concrete.Handle.handle translate to α.
--
-- Take the increasing round, for example, we need something like the following
-- property, which should be provided from the system layer:

  IncreasingRound : Set
  IncreasingRound 
    = ∀ {α v v'}
    → (ec1 : EpochConfig)
    → ∀ {αabs}
    → isAuthor ec1 α ≡ just αabs
    → Honest ec1 αabs
    → v  ^∙ vmVote ∙ vAuthor ≡ α → HasBeenSent (V v)  → WithVerSig v
    → v' ^∙ vmVote ∙ vAuthor ≡ α → HasBeenSent (V v') → WithVerSig v'
    → v  ^∙ vmProposed ∙ biEpoch ≡ v' ^∙ vmProposed ∙ biEpoch
    → unsafeReadMeta (v ^∙ vmVote ∙ vOrder) <VO unsafeReadMeta (v' ^∙ vmVote ∙ vOrder)
    → v ^∙ vmProposed ∙ biRound < v ^∙ vmProposed ∙ biRound

 {- Below is a copy of the relevant notes from the old BlockTree.agda 


  -----------------------------------------------------------------------------
  -- TEMPORARY: Properties we will need from the syste's layer as postulates --
  -----------------------------------------------------------------------------

  -- VCM: I'm writing postulates for now with the intent of making clear exactly where
  -- the proof is. The idea is that later we can move this postulate to a module parameter
  -- and we know exactly the invariants we need to ensure at the algorithmic level. 


  -- In the vote-order lemma for QCs, I can ulfold and extract information all the way
  -- to having proof that α issued the same voteOrder to vote for two different blocks.
  -- But we also have that α is honest, so this shouldn't be possible.
  --
  -- I'm not too worried about how we plan on putting the pieces together for now.
  -- so I suggest that we keep these postulates as long as we agree that these postulates
  -- represent states and actions that will never be seen or performed by a node running 
  -- our code.

  -- MSM: I agree with your commit comment that this "might be a good
  -- place to stop and think about how to connect the pieces".  Trying to
  -- push through proofs that we know cannot go through may indeed help
  -- to narrow down to cases we need "externally".  However, we might
  -- also make the proofs more complicated than they need to be by trying
  -- to narrow down to specific properties that are sufficient, and there
  -- is no guarantee that those properties are natural ones to prove
  -- about the concrete implementation.  Rather, I think we should think
  -- about what properties the implementation provides, because I think
  -- they should come much closer to handing us what we need on a plate,
  -- this keeping the proofs here simpler.  Below are some attempts to
  -- sketch out the properties I think are needed.


  postulate
    α-BROKE-VOTES-ONCE : ∀{bt α q q'} 
                       → (Abs.Q q) ∈BT bt → (Abs.Q q') ∈BT bt
                       → (va  : α Abs.∈QC q)(va' : α Abs.∈QC q') 
                       → Abs.voteOrder (Abs.∈QC-Vote q va) ≡ Abs.voteOrder (Abs.∈QC-Vote q' va')
                       → Abs.qCertBlockId q ≢ Abs.qCertBlockId q'
                       → ⊥

    α-BROKE-VOTES-INCR : ∀{bt α q q'} 
                       → (Abs.Q q) ∈BT bt → (Abs.Q q') ∈BT bt
                       → (va  : α Abs.∈QC q)(va' : α Abs.∈QC q') 
                       → q ≋QC q'
                       → Abs.voteOrder (Abs.∈QC-Vote q va) < Abs.voteOrder (Abs.∈QC-Vote q' va')
                       → ⊥


    {-- Here is a first attempt to sketch what system properties might be
        reqiured to enable proving the BlockTree properties are satisfied
        by the concrete implementation.  Rather than postulating
        properties here, properties that are proved about the concrete
        implementation should be parameters of this module.
    --}


    -- First we postulate a number of types just for the sake of being able to express some invariants here,
    -- without yet putting everything in the right place, right imports and parameters, etc.
    SystemState  : Set
    SentMessages : Set
    sentMessages : SystemState → SentMessages
    _∈SM_ : VoteMsg → SentMessages → Set
    HashValueZero : HashValue
    hashB : Block → HashValue

    {-
    The following two properties state what honest peers ensure about the
    votes they send.  From the perspective of a peer that receives these
    votes (either directly, or in QCs), these properties provide what is
    needed for establishing the properties needed to instantiate
    LibraBFT.Abstract.RecordChain.Properties.WithRSS in order to ensure
    (using thmS5) that commits are correct.  In both cases, the required
    property (IncreasingRoundRule or LockedRoundRule) is about votes in
    QCs, and the relevant property below (IncreasingRoundRuleInvariant or
    LockedRoundRuleInvariant, respectively) addresses the conditions
    under which these votes could be sent (by an honest peer).  To prove
    the properties required by
    LibraBFT.Abstract.RecordChain.Properties.WithRSS, we will show that
    the votes in the relevant QCs must have been sent, and then invoke
    the relevant property below to use the fact that a quorum contains a
    vote by honest peer to infer the required properties of the QCs.

    These are pretty ugly for a couple of reasons.  One is that I haven't
    (yet?) bothered with composite lenses, so there are long chains of
    lenses composed to state the properties.  More importantly, however,
    I think we can significantly simplify the properties by using
    abstract concepts like RecordChain and 𝕂-chain.  However, as it
    stands, we are not able to use properties about these types because
    they will refer to RecordChains and 𝕂-chains in *different*
    BlockTreees, whereas our properties apply only to a single BlockTree.
    Without changing this, we'll need to break the chains down into
    specific properties that we then use in another BlockTree to build up
    the required type.  I think we should restructure so that we can have
    properties that refer to different BlockTrees.  Take, for example,
    𝕂-chain-∈RC, which relates two different RecordChains.  However,
    these must be in the *same* RSS.  But we should be able to have
    similar properties for two different RSS's.  If the same abstract
    record is in two different RSSs, then each RSS contains a RecordChain
    up to that record, and (unless there is an injectivity failure on
    block hashes), these two RecordChains must have the same blocks and
    equivalent QCs.  Thus, we could state the moral equivalent of
    LockedRoundRuleInvariant in terms of an existentially quantified RSS
    with a RecordChain ending at the block being voted on.  In the proof
    of LockedRoundRule itself, we would establish that the same block
    exists in the RSS of the peer that sees the QCs that include the
    relevant votes.  We could then invoke the relevant invariant below to
    get the properties required.

    I'm not 100% sure it would be simpler to prove, but I certainly think
    it would make for cleaner, more understandable definitions.  But I
    want to get your thoughts on this Victor.  If you think it makes
    sense, you could consider teasing apart properties that relate
    different RecordChains and 𝕂-chain so that they are not restricted to
    be in the same RSS.

    One issue is that we will need to allow for an injectivity failure
    possibility that we preclude within a single RSS using the canInsert
    requirement.  This is unavoidable because, in case two different
    peers see different blocks that hash to the same value, neither is
    aware of the other's, so we can't guarantee that the two RecordChains
    (for example) have the same blocks: we can only ensure this if there
    are no hash collisions.

    -}

    IncreasingRoundRuleInvariant : ∀ {sysState α v v' epochId b1Info b1'Info}
                       → (ec1 : EpochConfig)
                       → ∀ {αabs}
                       → isAuthor ec1 α ≡ just αabs
                       → Honest ec1 αabs
                       → v  ^∙ vmVote ∙ vAuthor ≡ α → v  ∈SM sentMessages sysState → WithVerSig v
                       → v' ^∙ vmVote ∙ vAuthor ≡ α → v' ∈SM sentMessages sysState → WithVerSig v'
                       → v  ^∙ vmVote ∙ vVoteData ∙ vdProposed ∙ biEpoch ≡ epochId
                       → v' ^∙ vmVote ∙ vVoteData ∙ vdProposed ∙ biEpoch ≡ epochId
                       → b1Info  ≡ v  ^∙ vmVote ∙ vVoteData ∙ vdProposed
                       → b1'Info ≡ v' ^∙ vmVote ∙ vVoteData ∙ vdProposed
                       → unsafeReadMeta (v ^∙ vmVote ∙ vOrder) <VO unsafeReadMeta (v' ^∙ vmVote ∙ vOrder)
                       → b1Info ^∙ biRound < b1'Info ^∙ biRound

    LockedRoundRuleInvariant : ∀ {sysState α v v' epochId b1Info b1 b2Info b1'Info}
                       → (ec1 : EpochConfig)
                       → ∀ {αabs}
                       → isAuthor ec1 α ≡ just αabs
                       → Honest ec1 αabs
                       → v  ^∙ vmVote ∙ vAuthor ≡ α → v  ∈SM sentMessages sysState → WithVerSig v
                       → v' ^∙ vmVote ∙ vAuthor ≡ α → v' ∈SM sentMessages sysState → WithVerSig v'
                       → v  ^∙ vmVote ∙ vVoteData ∙ vdProposed ∙ biEpoch ≡ epochId
                       → v' ^∙ vmVote ∙ vVoteData ∙ vdProposed ∙ biEpoch ≡ epochId
                         -- Conditions for v
                       → b1Info ≡ v  ^∙ vmVote ∙ vVoteData ∙ vdProposed
                       → hashB b1 ≡ b1Info ^∙ biId
                       → b2Info ≡ b1 ^∙ bBlockData ∙ bdQuorumCert ∙ qcVoteData ∙ vdParent
                       → b2Info ^∙ biId ≢ HashValueZero  -- α had a 2-chain ending at q1  when it signed v
                         -- Conditions for v'
                       → b1'Info ≡ v' ^∙ vmVote ∙ vVoteData ∙ vdProposed
                       → b1'Info ^∙ biId ≢ HashValueZero -- α had a 1-chain ending at q1' when it signed v'
                         -- Vote order
                       → (unsafeReadMeta (v ^∙ vmVote ∙ vOrder)) <VO (unsafeReadMeta (v' ^∙ vmVote ∙ vOrder))
                         -- Unless HashBroke, the votes respect the LockedRoundRule
                       → HashBroke ⊎ b2Info ^∙ biRound < b1'Info ^∙ biRound

  {--

   NOTES:

     - We will need to assume/postulate for now that two honest peers
       have the same EpochConfig for the same epoch; later we will need
       to prove this.

     - HashBroke should be specific injectivity failure for block hashes

     - Because an honest peer assigns to a new vote a VoteOrder higher
       than all previous ones, if a new vote satisfies the conditions to
       be v here, then the last clause of the antecedent does not hold
       afterwards because v' cannot exist

     - Suppose a new vote satisfies the conditions to be v' and there is
       already a vote satisfying the conditions for v, this would
       potentially falsify the invariant, so we need to show that this
       cannot happen.  This is where we formalize the fact that an honest
       peer obeys the LockedRoundRule.

       - We need an invariant that says that, if α has previously sent a
         vote satisfying the conditions for v, then α will not send a vote
         satisfying the conditions for v'.

  --}


  {- If we are about to construct a vote satisfying the conditions for v'
  and we've already sent a vote satisfying the conditions for v, then
  there is a contradiction because of the preferedRound rule.  Here are
  sketches of some invariants we might use to prove this.  This is just
  for concreteness in thiking about how the proof will hang together; it
  probably doesn't make sense to get into too much detail proving these
  before settling down the "interface" between the concrete
  implementation and some version of the LockedRoundRulePromise, which
  should be provided as a parameter to this module, not postulated.

  -}

  postulate
    PeerId : Set
    EventProcessor : Set
    peerStates : SystemState → KVMap PeerId EventProcessor
    epSafetyRules : EventProcessor → SafetyRules
    epPreferredRound : Lens EventProcessor Round
    epBlockTree : Lens EventProcessor BlockTree

  WontViolateLockedRoundRule : SystemState → Set
  WontViolateLockedRoundRule st = ∀ {α v v' epochId b1 b1Info b2Info b1'Info to ts pSt}
                       → (p : PeerId)
                       → lookup p (peerStates st) ≡ just pSt
                       → v  ^∙ vmVote ∙ vAuthor ≡ α → v ∈SM sentMessages st → WithVerSig v
                       → v  ^∙ vmVote ∙ vVoteData ∙ vdProposed ∙ biEpoch ≡ epochId

                       -- Conditions for v
                       → b1Info ≡ v  ^∙ vmVote ∙ vVoteData ∙ vdProposed
                       → hashB b1 ≡ b1Info ^∙ biId
                       → b2Info ≡ b1 ^∙ bBlockData ∙ bdQuorumCert ∙ qcVoteData ∙ vdParent
                       → b2Info ^∙ biId ≢ HashValueZero  -- α had a 2-chain ending at q1  when it signed v
                       → v' ^∙ vmVote ∙ vVoteData ∙ vdProposed ∙ biEpoch ≡ epochId
                       → b1'Info ≡ v' ^∙ vmVote ∙ vVoteData ∙ vdProposed
                       → b1'Info ^∙ biId ≢ HashValueZero -- α had a 1-chain ending at q1' when it signed v'
                         -- Relating rounds of relevant previous records for v and v'
                       → b1'Info ^∙ biRound < b2Info ^∙ biRound
                       → {! (send v' to) ∈ proj₂ (pureHandler msg ts pSt)  !} {- Handler actions include sending a vote satisfying conditions of v' in LockerRoundRulePromise -}
                       → ⊥


  {- Notes:

     * We do not need to assume α is honest here.  Because the invariant
       applies to a peer's state, it can be falsified only by steps of an
       honest peer (cheat steps do not modify peer states).  However, we
       will still need to relate the state to the EpochConfig using α-EC.

     * This is an invariant only on α's state: it does not need to refer
       to anything else (sent messages, other peers' states); it may be
       worth standardizing such cases, so we don't need to refer
       explicitly to the prestate being in the SystemState.  But for now,
       follow pattern from original example invariant.

     * I suspect it will make sense to refer to abstract records,
       RecordChains, etc.  However, properties we have about these refer
       only to a single abstract blocktree.  For example, the two
       RecordChains referred to by the statement of 𝕂-chain-∈RC must both
       be for the same RSS.  Therefore, we cannot use it to prove that if
       a given record is in one peer's BlockTree, and the same record is
       in another peer's BlockTree, then the two recordchains must
       include the same blocks (unless there is an injectivity failure on
       blocks).  I am sticking to everything concrete here to make
       progress.

     * The consequent should hold even for the first QC added, because
       the parent block info will have round 0

  -}

  PreferredRoundCorrect : SystemState → Set
  PreferredRoundCorrect st = ∀ {pSt qc isValid blkHash}
                        → (p : PeerId)
                        → lookup p (peerStates st) ≡ just pSt
                        → lookup blkHash (pSt ^∙ epBlockTree ∙ btIdToQuorumCert) ≡ just ( qc , isValid )
                        → pSt ^∙ epPreferredRound ≥ qc ^∙ qcParentBlock ∙ biRound

  
-}
