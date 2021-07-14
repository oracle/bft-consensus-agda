{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module contains definitions of properties of only the behavior of the
-- handlers, nothing concerning the system state.

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.KVMap as Map
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.ConsensusTypes.Block as Block
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId

module LibraBFT.Impl.Consensus.RoundManager.PropertyDefs where

module OutputProps where
  module _ (outs : List Output) where
    None : Set
    None = outs ≡ []

    NoneOfKind : ∀ {ℓ} {P : Output → Set ℓ} (p : (out : Output) → Dec (P out)) → Set
    NoneOfKind p = List-filter p outs ≡ []

    NoVotes      = NoneOfKind isSendVote?
    NoBroadcasts = NoneOfKind isBroadcastProposal?
    NoMsgs       = NoneOfKind isOutputMsg?
    NoErrors     = NoneOfKind isLogErr?

    NoMsgs⇒× : NoMsgs → NoBroadcasts × NoVotes
    NoMsgs⇒× noMsgs
      rewrite filter-∪?-[]₁ outs isBroadcastProposal? isSendVote? noMsgs
      |       filter-∪?-[]₂ outs isBroadcastProposal? isSendVote? noMsgs
      = refl , refl

    NoMsgs⇒NoBroadcasts = proj₁ ∘ NoMsgs⇒×
    NoMsgs⇒NoVotes      = proj₂ ∘ NoMsgs⇒×

    OneVote : VoteMsg → List Author → Set
    OneVote vm pids = List-filter isSendVote? outs ≡ (SendVote vm pids ∷ [])

  ++-NoneOfKind : ∀ {ℓ} {P : Output → Set ℓ} xs ys (p : (out : Output) → Dec (P out))
                  → NoneOfKind xs p → NoneOfKind ys p → NoneOfKind (xs ++ ys) p
  ++-NoneOfKind xs ys p nok₁ nok₂ = filter-++-[] xs ys p nok₁ nok₂

  ++-NoMsgs       = λ xs ys → ++-NoneOfKind xs ys isOutputMsg?
  ++-NoVotes      = λ xs ys → ++-NoneOfKind xs ys isSendVote?
  ++-NoBroadcasts = λ xs ys → ++-NoneOfKind xs ys isBroadcastProposal?

  ++-NoVotes-OneVote : ∀ xs ys {vm} {pids} → NoVotes xs → OneVote ys vm pids
                       → OneVote (xs ++ ys) vm pids
  ++-NoVotes-OneVote xs ys nv ov
    rewrite List-filter-++ isSendVote? xs ys
    |       nv = ov

  ++-OneVote-NoVotes : ∀ xs {vm pids} ys → OneVote xs vm pids → NoVotes ys
                       → OneVote (xs ++ ys) vm pids
  ++-OneVote-NoVotes xs ys ov nv
    rewrite List-filter-++ isSendVote? xs ys
    |       nv
    |       ov = refl

module StateInvariants where
  -- The property that a block tree `bt` has only valid QCs with respect to epoch config `𝓔`
  AllValidQCs : (𝓔 : EpochConfig) (bt : BlockTree) → Set
  AllValidQCs 𝓔 bt = (hash : HashValue) → maybe (WithEC.MetaIsValidQC 𝓔) ⊤ (lookup hash (bt ^∙ btIdToQuorumCert))

  module _ (rm : RoundManager) where
    EpochsMatch : Set
    EpochsMatch = rm ^∙ rmEpochState ∙ esEpoch ≡ rm ^∙ lSafetyData ∙ sdEpoch

    record BlockTreeInv : Set where
      constructor mkBlockTreeInv
      field
        allValidQCs : (rmC : RoundManager-correct rm) → AllValidQCs (α-EC-RM rm rmC) (rm ^∙ rmBlockStore ∙ bsInner)

    -- NOTE: This will be proved by induction on reachable states using the
    -- property that peer handlers preserve invariants. That is to say, many of
    -- these cannot be proven as a post-condition of the peer handler: one can
    -- only prove of the handler that if the invariant holds for the prestate,
    -- then it holds for the poststate.
    record RoundManagerInv : Set where
      constructor mkRoundManagerInv
      field
        rmCorrect    : RoundManager-correct rm
        blockTreeInv : BlockTreeInv
        epochsMatch  : EpochsMatch

  Preserves : ∀ {ℓ} → (P : RoundManager → Set ℓ) (pre post : RoundManager) → Set ℓ
  Preserves Pred pre post = Pred pre → Pred post

  reflPreserves : ∀ {ℓ} (P : RoundManager → Set ℓ) → Reflexive (Preserves P)
  reflPreserves Pred = id

  reflPreservesRoundManagerInv = reflPreserves RoundManagerInv

  transPreserves : ∀ {ℓ} (P : RoundManager → Set ℓ) → Transitive (Preserves P)
  transPreserves Pred p₁ p₂ = p₂ ∘ p₁

  transPreservesRoundManagerInv = transPreserves RoundManagerInv

  mkPreservesRoundManagerInv
    : ∀ {pre post}
      → Preserves RoundManager-correct pre post
      → Preserves BlockTreeInv         pre post
      → Preserves EpochsMatch          pre post
      → Preserves RoundManagerInv      pre post
  mkPreservesRoundManagerInv prmC pbti pep (mkRoundManagerInv rmCorrect blockTreeInv epochsMatch) =
    mkRoundManagerInv (prmC rmCorrect) (pbti blockTreeInv) (pep epochsMatch)

module StateProps where
  -- Relations between the pre/poststate which may or may not hold, depending on
  -- the particular peer handler invoked

  -- - The epoch is unchanged
  NoEpochChange : (pre post : RoundManager) → Set
  NoEpochChange pre post = pre ≡L post at rmEpoch

  reflNoEpochChange : Reflexive NoEpochChange
  reflNoEpochChange = refl

  transNoEpochChange : Transitive NoEpochChange
  transNoEpochChange = trans

  -- - state changes from generating or not generating a vote
  LastVoteIs : RoundManager → Vote → Set
  LastVoteIs rm v = just v ≡ rm ^∙ lSafetyData ∙ sdLastVote

  module _ (pre post : RoundManager) (vote : Vote) where

    record VoteOldGenerated : Set where
      constructor mkVoteOldGenerated
      field
        lvr≡ : pre ≡L post at lSafetyData ∙ sdLastVotedRound
        lv≡  : pre ≡L post at lSafetyData ∙ sdLastVote

    record VoteNewGenerated : Set where
      constructor mkVoteNewGenerated
      field
        lvr< : pre [ _<_ ]L post at lSafetyData ∙ sdLastVotedRound
        lvr≡ : vote ^∙ vRound ≡ post ^∙ lSafetyData ∙ sdLastVotedRound

    -- NOTE: This is saying that /state changes/ associated to generating a vote
    -- have occurred, not that the generated vote has been sent.
    record VoteGenerated : Set where
      constructor mkVoteGenerated
      field
        lv≡v    : LastVoteIs post vote
        voteSrc : VoteOldGenerated ⊎ VoteNewGenerated

    isVoteNewGenerated : VoteGenerated → Bool
    isVoteNewGenerated = isRight ∘ VoteGenerated.voteSrc

  reflVoteOldGenerated : ∀ {v} → Reflexive (λ pre post → VoteOldGenerated pre post v)
  reflVoteOldGenerated = mkVoteOldGenerated refl refl

  VoteGeneratedNotSaved : (pre post : RoundManager) → Set
  VoteGeneratedNotSaved pre post = ∃[ v ] VoteGenerated pre post v

  module _ (pre post : RoundManager) where
    -- In
    -- `LibraBFT.Impl.Consensus.SafetyRules.SafetyRules.agda::contructAndSignVoteM`,
    -- it is possible for us to update the field `lSafetyData ∙ sdLastVotedRound`
    -- without actually returning a vote. Therefore, the most we can say after
    -- returing from this function is that this field in the poststate is greater
    -- than or equal to the value it started at in the prestate.
    --
    -- However, it is also possible to return a vote *without* updating the last
    -- voted round. Many functions in `LibraBFT.Impl.Consensus.RoundManager` neither
    -- return a vote nor update the last voted round, and the lemma
    -- `pseudotransVoteSent` in those cases -- but is unprovable if we do not
    -- distinguish the cases where the last voted round cannot be increased.
    -- Therefore, it is convenient to track in the type of `NoVoteSent`, with the
    -- parameter `lvr≡?`, which case we are dealing with
    record VoteNotGenerated  (lvr≡? : Bool) : Set where
      constructor mkVoteNotGenerated
      field
        lv≡  : pre ≡L post at lSafetyData ∙ sdLastVote
        lvr≤ : pre [ if lvr≡? then _≡_ else _<_ ]L post at lSafetyData ∙ sdLastVotedRound

  reflVoteNotGenerated : Reflexive (λ pre post → VoteNotGenerated pre post true)
  reflVoteNotGenerated = mkVoteNotGenerated refl refl

  transVoteNotGenerated
    : ∀ {s₁ s₂ s₃ lvr≡?₁ lvr≡?₂}
      → VoteNotGenerated s₁ s₂ lvr≡?₁ → VoteNotGenerated s₂ s₃ lvr≡?₂
      → VoteNotGenerated s₁ s₃ (lvr≡?₁ ∧ lvr≡?₂)
  transVoteNotGenerated {lvr≡?₁ = false} {false} (mkVoteNotGenerated lv≡ lvr≤) (mkVoteNotGenerated lv≡₁ lvr≤₁) =
    mkVoteNotGenerated (trans lv≡ lv≡₁) (<-trans lvr≤ lvr≤₁)
  transVoteNotGenerated {lvr≡?₁ = false} {true} (mkVoteNotGenerated lv≡ lvr≤) (mkVoteNotGenerated lv≡₁ lvr≤₁) =
    mkVoteNotGenerated (trans lv≡ lv≡₁) (≤-trans lvr≤ (≡⇒≤ lvr≤₁))
  transVoteNotGenerated {lvr≡?₁ = true} {false} (mkVoteNotGenerated lv≡ lvr≤) (mkVoteNotGenerated lv≡₁ lvr≤₁) =
    mkVoteNotGenerated (trans lv≡ lv≡₁) (≤-trans (s≤s (≡⇒≤ lvr≤)) lvr≤₁)
  transVoteNotGenerated {lvr≡?₁ = true} {true} (mkVoteNotGenerated lv≡ lvr≤) (mkVoteNotGenerated lv≡₁ lvr≤₁) =
    mkVoteNotGenerated (trans lv≡ lv≡₁) (trans lvr≤ lvr≤₁)

  step-VoteGenerated-VoteNotGenerated
    : ∀ {s₁ s₂ s₃ v} → VoteGenerated s₁ s₂ v → VoteNotGenerated s₂ s₃ true
      → VoteGenerated s₁ s₃ v
  step-VoteGenerated-VoteNotGenerated (mkVoteGenerated lv≡v (inj₁ (mkVoteOldGenerated lvr≡₁ lv≡₁))) (mkVoteNotGenerated lv≡ lvr≤) =
    mkVoteGenerated (trans lv≡v lv≡) (inj₁ (mkVoteOldGenerated (trans lvr≡₁ lvr≤) (trans lv≡₁ lv≡)))
  step-VoteGenerated-VoteNotGenerated (mkVoteGenerated lv≡v (inj₂ (mkVoteNewGenerated lvr< lvr≡))) (mkVoteNotGenerated lv≡ lvr≤) =
    mkVoteGenerated ((trans lv≡v lv≡)) (inj₂ (mkVoteNewGenerated (≤-trans lvr< (≡⇒≤ lvr≤)) (trans lvr≡ lvr≤)))

  step-VoteNotGenerated-VoteGenerated
    : ∀ {s₁ s₂ s₃ v} → VoteNotGenerated s₁ s₂ true → VoteGenerated s₂ s₃ v
      → VoteGenerated s₁ s₃ v
  step-VoteNotGenerated-VoteGenerated (mkVoteNotGenerated lv≡ lvr≤) (mkVoteGenerated lv≡v (inj₁ (mkVoteOldGenerated lvr≡₁ lv≡₁))) =
    mkVoteGenerated lv≡v (inj₁ (mkVoteOldGenerated (trans lvr≤ lvr≡₁) (trans lv≡ lv≡₁)))
  step-VoteNotGenerated-VoteGenerated (mkVoteNotGenerated lv≡ lvr≤) (mkVoteGenerated lv≡v (inj₂ (mkVoteNewGenerated lvr<₁ lvr≡₁))) =
    mkVoteGenerated lv≡v (inj₂ (mkVoteNewGenerated (≤-trans (s≤s (≡⇒≤ lvr≤)) lvr<₁) lvr≡₁))

  step-VoteNotGenerated-VoteGeneratedNotSaved
    : ∀ {s₁ s₂ s₃} → VoteNotGenerated s₁ s₂ true → VoteGeneratedNotSaved s₂ s₃
      → VoteGeneratedNotSaved s₁ s₃
  step-VoteNotGenerated-VoteGeneratedNotSaved vng (v , vg) =
    v , step-VoteNotGenerated-VoteGenerated vng vg

-- Properties for voting
module Voting where

  VoteEpochIs : (vote : Vote) (e : Epoch) → Set
  VoteEpochIs vote e = vote ^∙ vEpoch ≡ e

  VoteRoundIs : (vote : Vote) (r : Round) → Set
  VoteRoundIs vote r = vote ^∙ vRound ≡ r

  record VoteMadeFromBlock (vote : Vote) (block : Block) : Set where
    constructor mkVoteMadeFromBlock
    field
      epoch≡ : vote ^∙ vEpoch ≡ block ^∙ bEpoch
      round≡ : vote ^∙ vRound ≡ block ^∙ bRound
      proposedID : vote ^∙ vProposedId ≡ block ^∙ bId

  VoteMadeFromBlock⇒VoteEpochRoundIs : ∀ {v b} → VoteMadeFromBlock v b → VoteEpochIs v (b ^∙ bEpoch) × VoteRoundIs v (b ^∙ bRound)
  VoteMadeFromBlock⇒VoteEpochRoundIs (mkVoteMadeFromBlock epoch≡ round≡ proposedID) = epoch≡ , round≡

  VoteTriggeredByBlock : (vote : Vote) (block : Block) (new? : Bool) → Set
  VoteTriggeredByBlock vote block true = VoteMadeFromBlock vote block
  VoteTriggeredByBlock vote block false = VoteRoundIs vote (block ^∙ bRound)

  record VoteGeneratedCorrect (pre post : RoundManager) (vote : Vote) (block : Block) : Set where
    constructor mkVoteGeneratedCorrect
    field
      state          : StateProps.VoteGenerated pre post vote
    voteNew? = StateProps.isVoteNewGenerated pre post vote state
    field
      blockTriggered : VoteTriggeredByBlock vote block voteNew?

  record VoteGeneratedUnsavedCorrect (pre post : RoundManager) (block : Block) : Set where
    constructor mkVoteGeneratedUnsavedCorrect
    field
      vote           : Vote
      voteGenCorrect : VoteGeneratedCorrect pre post vote block

  step-VoteGeneratedCorrect-VoteNotGenerated
    : ∀ {s₁ s₂ s₃ vote block}
      → VoteGeneratedCorrect s₁ s₂ vote block
      → StateProps.VoteNotGenerated s₂ s₃ true
      → VoteGeneratedCorrect s₁ s₃ vote block
  step-VoteGeneratedCorrect-VoteNotGenerated vgc@(mkVoteGeneratedCorrect vg@(StateProps.mkVoteGenerated lv≡v (inj₁ oldVG)) blockTriggered) vng =
    mkVoteGeneratedCorrect (StateProps.step-VoteGenerated-VoteNotGenerated vg vng) blockTriggered
  step-VoteGeneratedCorrect-VoteNotGenerated vgc@(mkVoteGeneratedCorrect vg@(StateProps.mkVoteGenerated lv≡v (inj₂ newVG)) blockTriggered) vng =
    mkVoteGeneratedCorrect (StateProps.step-VoteGenerated-VoteNotGenerated vg vng) blockTriggered

  step-VoteNotGenerated-VoteGeneratedCorrect
    : ∀ {s₁ s₂ s₃ vote block}
      → StateProps.VoteNotGenerated s₁ s₂ true
      → VoteGeneratedCorrect s₂ s₃ vote block
      → VoteGeneratedCorrect s₁ s₃ vote block
  step-VoteNotGenerated-VoteGeneratedCorrect vng (mkVoteGeneratedCorrect vg@(StateProps.mkVoteGenerated lv≡v (Left oldVG)) blockTriggered) =
    mkVoteGeneratedCorrect (StateProps.step-VoteNotGenerated-VoteGenerated vng vg) blockTriggered
  step-VoteNotGenerated-VoteGeneratedCorrect vng (mkVoteGeneratedCorrect vg@(StateProps.mkVoteGenerated lv≡v (Right newVG)) blockTriggered) =
    mkVoteGeneratedCorrect (StateProps.step-VoteNotGenerated-VoteGenerated vng vg)
      blockTriggered

  step-VoteNotGenerated-VoteGeneratedUnsavedCorrect
    : ∀ {s₁ s₂ s₃ block}
      → StateProps.VoteNotGenerated s₁ s₂ true
      → VoteGeneratedUnsavedCorrect s₂ s₃ block
      → VoteGeneratedUnsavedCorrect s₁ s₃ block
  step-VoteNotGenerated-VoteGeneratedUnsavedCorrect vng (mkVoteGeneratedUnsavedCorrect vote voteGenCorrect) =
    mkVoteGeneratedUnsavedCorrect vote (step-VoteNotGenerated-VoteGeneratedCorrect vng voteGenCorrect)

  -- The handler correctly voted (including state updates) on `block`, assuming
  -- the safety data epoch matches the block epoch.
  record VoteSentCorrect (pre post : RoundManager) (outs : List Output) (block : Block) : Set where
    constructor mkVoteSentCorrect
    field
      vm           : VoteMsg
      pid          : Author
      voteMsgOuts  : OutputProps.OneVote outs vm (pid ∷ [])
      vgCorrect    : VoteGeneratedCorrect pre post (vm ^∙ vmVote) block
    open VoteGeneratedCorrect vgCorrect

  -- The handler correctly did not vote on `block`
  record VoteUnsentCorrect (pre post : RoundManager) (outs : List Output) (block : Block) (lvr≡? : Bool) : Set where
    constructor mkVoteUnsentCorrect
    field
      noVoteMsgOuts : OutputProps.NoVotes outs
      nvg⊎vgusc    : StateProps.VoteNotGenerated pre post lvr≡? ⊎ VoteGeneratedUnsavedCorrect pre post block

  step-VoteNotGenerated-VoteUnsentCorrect
    : ∀ {s₁ s₂ s₃ outs₁ outs₂ block lvr≡?}
      → StateProps.VoteNotGenerated s₁ s₂ true → OutputProps.NoVotes outs₁
      → VoteUnsentCorrect s₂ s₃ outs₂ block lvr≡?
      → VoteUnsentCorrect s₁ s₃ (outs₁ ++ outs₂) block lvr≡?
  step-VoteNotGenerated-VoteUnsentCorrect{outs₁ = outs₁} vng₁ nvo (mkVoteUnsentCorrect noVoteMsgOuts (Left vng₂)) =
    mkVoteUnsentCorrect (OutputProps.++-NoVotes outs₁ _ nvo noVoteMsgOuts) (Left (StateProps.transVoteNotGenerated vng₁ vng₂))
  step-VoteNotGenerated-VoteUnsentCorrect{outs₁ = outs₁} vng₁ nvo (mkVoteUnsentCorrect noVoteMsgOuts (Right vgus)) =
    mkVoteUnsentCorrect ((OutputProps.++-NoVotes outs₁ _ nvo noVoteMsgOuts)) (Right (step-VoteNotGenerated-VoteGeneratedUnsavedCorrect vng₁ vgus))

  -- The handler correctly attempted to vote on `block`, assuming the safety
  -- data epoch matches the block epoch.
  VoteAttemptCorrect : (pre post : RoundManager) (outs : List Output) (block : Block) → Set
  VoteAttemptCorrect pre post outs block =
    (∃[ lvr≡? ] VoteUnsentCorrect pre post outs block lvr≡?) ⊎ VoteSentCorrect pre post outs block

  -- The voting process ended before `lSafetyData` could be updated
  voteAttemptBailed : ∀ {rm block} outs → OutputProps.NoVotes outs → VoteAttemptCorrect rm rm outs block
  voteAttemptBailed outs noVotesOuts = Left (true , mkVoteUnsentCorrect noVotesOuts (Left StateProps.reflVoteNotGenerated))

  step-VoteNotGenerated-VoteAttemptCorrect
    : ∀ {s₁ s₂ s₃ outs₁ outs₂ block}
      → StateProps.VoteNotGenerated s₁ s₂ true → OutputProps.NoVotes outs₁
      → VoteAttemptCorrect s₂ s₃ outs₂ block
      → VoteAttemptCorrect s₁ s₃ (outs₁ ++ outs₂) block
  step-VoteNotGenerated-VoteAttemptCorrect{outs₁ = outs₁} vng nvo (Left (lvr≡? , vusCorrect)) =
    Left (lvr≡? , step-VoteNotGenerated-VoteUnsentCorrect{outs₁ = outs₁} vng nvo vusCorrect)
  step-VoteNotGenerated-VoteAttemptCorrect{outs₁ = outs₁} vng nvo (Right (mkVoteSentCorrect vm pid voteMsgOuts vgCorrect)) =
    Right (mkVoteSentCorrect vm pid (OutputProps.++-NoVotes-OneVote outs₁ _ nvo voteMsgOuts) (step-VoteNotGenerated-VoteGeneratedCorrect vng vgCorrect))

  VoteAttemptEpochReq : ∀ {pre post outs block} → VoteAttemptCorrect pre post outs block → Set
  VoteAttemptEpochReq (Left (_ , mkVoteUnsentCorrect _ (Left _))) =
    ⊤
  VoteAttemptEpochReq{pre}{block = block} (Left (_ , mkVoteUnsentCorrect _ (Right _))) =
    pre ^∙ lSafetyData ∙ sdEpoch ≡ (block ^∙ bEpoch)
  VoteAttemptEpochReq{pre}{block = block} (Right _) =
    pre ^∙ lSafetyData ∙ sdEpoch ≡ (block ^∙ bEpoch)

  voteAttemptEpochReq!
    : ∀ {pre post outs block} → (vac : VoteAttemptCorrect pre post outs block)
      → pre ^∙ lSafetyData ∙ sdEpoch ≡ block ^∙ bEpoch → VoteAttemptEpochReq vac
  voteAttemptEpochReq! (Left (_ , mkVoteUnsentCorrect _ (Left _))) eq = tt
  voteAttemptEpochReq! (Left (_ , mkVoteUnsentCorrect _ (Right _))) eq = eq
  voteAttemptEpochReq! (Right _) eq = eq

  record VoteAttemptCorrectWithEpochReq (pre post : RoundManager) (outs : List Output) (block : Block) : Set where
    constructor mkVoteAttemptCorrectWithEpochReq
    field
      voteAttempt : VoteAttemptCorrect pre post outs block
      sdEpoch≡?   : VoteAttemptEpochReq voteAttempt
