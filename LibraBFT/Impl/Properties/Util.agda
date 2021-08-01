{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

-- This module contains definitions of properties of only the behavior of the
-- handlers, nothing concerning the system state.

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.KVMap as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Consensus.ConsensusTypes.Block as Block
open import LibraBFT.Impl.Handle
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open        ParamsWithInitAndHandlers InitAndHandlers
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers
                               PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})

module LibraBFT.Impl.Properties.Util where

module Meta where
  getLastVoteEpoch : RoundManager → Epoch
  getLastVoteEpoch rm = maybe{B = const Epoch} (_^∙ vEpoch) (rm ^∙ pssSafetyData-rm ∙ sdEpoch) ∘ (_^∙ pssSafetyData-rm ∙ sdLastVote) $ rm

  getLastVoteRound : RoundManager → Round
  getLastVoteRound = maybe{B = const Round} (_^∙ vRound) 0 ∘ (_^∙ pssSafetyData-rm ∙ sdLastVote)

module OutputProps where
  module _ (outs : List Output) where
    None : Set
    None = outs ≡ []

    NoVotes     = NoneOfKind outs isSendVote?
    NoProposals = NoneOfKind outs isBroadcastProposal?
    NoSyncInfos = NoneOfKind outs isBroadcastSyncInfo?
    NoMsgs      = NoneOfKind outs isOutputMsg?
    NoErrors    = NoneOfKind outs isLogErr?

    NoMsgs⇒× : NoMsgs → NoProposals × NoVotes × NoSyncInfos
    proj₁ (NoMsgs⇒× noMsgs) =
      filter-∪?-[]₁ outs isBroadcastProposal? _
        (filter-∪?-[]₁ outs _ _ noMsgs)
    proj₁ (proj₂ (NoMsgs⇒× noMsgs)) =
      filter-∪?-[]₂ outs _ isSendVote? noMsgs
    proj₂ (proj₂ (NoMsgs⇒× noMsgs)) =
      filter-∪?-[]₂ outs _ isBroadcastSyncInfo?
        (filter-∪?-[]₁ outs _ _ noMsgs)

    NoMsgs⇒NoProposals : NoMsgs → NoProposals
    NoMsgs⇒NoProposals = proj₁ ∘ NoMsgs⇒×

    NoMsgs⇒NoVotes : NoMsgs → NoVotes
    NoMsgs⇒NoVotes = proj₁ ∘ proj₂ ∘ NoMsgs⇒×

    OneVote : VoteMsg → List Author → Set
    OneVote vm pids = List-filter isSendVote? outs ≡ (SendVote vm pids ∷ [])

  ++-NoneOfKind : ∀ {ℓ} {P : Output → Set ℓ} xs ys (p : (out : Output) → Dec (P out))
                  → NoneOfKind xs p → NoneOfKind ys p → NoneOfKind (xs ++ ys) p
  ++-NoneOfKind xs ys p nok₁ nok₂ = filter-++-[] xs ys p nok₁ nok₂

  ++-NoMsgs      = λ xs ys → ++-NoneOfKind xs ys isOutputMsg?
  ++-NoVotes     = λ xs ys → ++-NoneOfKind xs ys isSendVote?
  ++-NoProposals = λ xs ys → ++-NoneOfKind xs ys isBroadcastProposal?

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
    EpochsMatch = rm ^∙ rmEpochState ∙ esEpoch ≡ rm ^∙ pssSafetyData-rm ∙ sdEpoch

    record BlockStoreInv : Set where
      constructor mkBlockTreeInv
      field
        allValidQCs : (rmC : RoundManager-correct rm) → AllValidQCs (α-EC-RM rm rmC) (rm ^∙ rmBlockStore ∙ bsInner)

    -- SafetyRules invariants
    record SafetyDataInv : Set where
      constructor mkSafetyDataInv
      field
        lvEpoch≡ : Meta.getLastVoteEpoch rm ≡ rm ^∙ pssSafetyData-rm ∙ sdEpoch
        lvRound≤ : Meta.getLastVoteRound rm ≤ rm ^∙ pssSafetyData-rm ∙ sdLastVotedRound

    record SafetyRulesInv : Set where
      constructor mkSafetyRulesInv
      field
        sdInv : SafetyDataInv

    -- NOTE: This will be proved by induction on reachable states using the
    -- property that peer handlers preserve invariants. That is to say, many of
    -- these cannot be proven as a post-condition of the peer handler: one can
    -- only prove of the handler that if the invariant holds for the prestate,
    -- then it holds for the poststate.
    record RoundManagerInv : Set where
      constructor mkRoundManagerInv
      field
        rmCorrect   : RoundManager-correct rm
        epochsMatch : EpochsMatch
        btInv       : BlockStoreInv
        srInv       : SafetyRulesInv

  Preserves : ∀ {ℓ} → (P : RoundManager → Set ℓ) (pre post : RoundManager) → Set ℓ
  Preserves Pred pre post = Pred pre → Pred post

  reflPreserves : ∀ {ℓ} (P : RoundManager → Set ℓ) → Reflexive (Preserves P)
  reflPreserves Pred = id

  reflPreservesRoundManagerInv = reflPreserves RoundManagerInv

  transPreserves : ∀ {ℓ} (P : RoundManager → Set ℓ) → Transitive (Preserves P)
  transPreserves Pred p₁ p₂ = p₂ ∘ p₁

  transPreservesRoundManagerInv = transPreserves RoundManagerInv

  substSafetyDataInv
    : ∀ {pre post} → pre ≡L post at pssSafetyData-rm → Preserves SafetyDataInv pre post
  substSafetyDataInv{pre}{post} sd≡ (mkSafetyDataInv epoch≡ round≤) = mkSafetyDataInv epoch≡' round≤'
    where
    epoch≡' : Meta.getLastVoteEpoch post ≡ post ^∙ pssSafetyData-rm ∙ sdEpoch
    epoch≡' rewrite sym sd≡ = epoch≡

    round≤' : Meta.getLastVoteRound post ≤ post ^∙ pssSafetyData-rm ∙ sdLastVotedRound
    round≤' rewrite sym sd≡ = round≤

  mkPreservesSafetyRulesInv
    : ∀ {pre post}
      → Preserves SafetyDataInv pre post
      → Preserves SafetyRulesInv pre post
  mkPreservesSafetyRulesInv lvP (mkSafetyRulesInv lv) = mkSafetyRulesInv (lvP lv)

  mkPreservesRoundManagerInv
    : ∀ {pre post}
      → Preserves RoundManager-correct pre post
      → Preserves EpochsMatch          pre post
      → Preserves BlockStoreInv        pre post
      → Preserves SafetyRulesInv       pre post
      → Preserves RoundManagerInv      pre post
  mkPreservesRoundManagerInv rmP emP bsP srP (mkRoundManagerInv rmCorrect epochsMatch btInv srInv) =
    mkRoundManagerInv (rmP rmCorrect) (emP epochsMatch) (bsP btInv) (srP srInv)

module StateTransProps where
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
  LastVoteIs rm v = just v ≡ rm ^∙ pssSafetyData-rm ∙ sdLastVote

  module _ (pre post : RoundManager) (vote : Vote) where

    record VoteOldGenerated : Set where
      constructor mkVoteOldGenerated
      field
        -- NOTE: The implementation maintains an invariant that the round
        -- associated with `sdLastVote` (if the vote exists) is less than or
        -- equal to the field `sdLastVotedRound`.
        lvr≡ : pre ≡L post at pssSafetyData-rm ∙ sdLastVotedRound
        lv≡  : pre ≡L post at pssSafetyData-rm ∙ sdLastVote

    record VoteNewGenerated : Set where
      constructor mkVoteNewGenerated
      field
        lvr< : pre [ _<_ ]L post at pssSafetyData-rm ∙ sdLastVotedRound
        lvr≡ : vote ^∙ vRound ≡ post ^∙ pssSafetyData-rm ∙ sdLastVotedRound

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
    -- it is possible for us to update the field `pssSafetyData-rm ∙ sdLastVotedRound`
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
        lv≡  : pre ≡L post at pssSafetyData-rm ∙ sdLastVote
        lvr≤ : pre [ if lvr≡? then _≡_ else _<_ ]L post at pssSafetyData-rm ∙ sdLastVotedRound

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

  glue-VoteGenerated-VoteNotGenerated
    : ∀ {s₁ s₂ s₃ v} → VoteGenerated s₁ s₂ v → VoteNotGenerated s₂ s₃ true
      → VoteGenerated s₁ s₃ v
  glue-VoteGenerated-VoteNotGenerated (mkVoteGenerated lv≡v (inj₁ (mkVoteOldGenerated lvr≡₁ lv≡₁))) (mkVoteNotGenerated lv≡ lvr≤) =
    mkVoteGenerated (trans lv≡v lv≡) (inj₁ (mkVoteOldGenerated (trans lvr≡₁ lvr≤) (trans lv≡₁ lv≡)))
  glue-VoteGenerated-VoteNotGenerated (mkVoteGenerated lv≡v (inj₂ (mkVoteNewGenerated lvr< lvr≡))) (mkVoteNotGenerated lv≡ lvr≤) =
    mkVoteGenerated ((trans lv≡v lv≡)) (inj₂ (mkVoteNewGenerated (≤-trans lvr< (≡⇒≤ lvr≤)) (trans lvr≡ lvr≤)))

  glue-VoteNotGenerated-VoteGenerated
    : ∀ {s₁ s₂ s₃ v} → VoteNotGenerated s₁ s₂ true → VoteGenerated s₂ s₃ v
      → VoteGenerated s₁ s₃ v
  glue-VoteNotGenerated-VoteGenerated (mkVoteNotGenerated lv≡ lvr≤) (mkVoteGenerated lv≡v (inj₁ (mkVoteOldGenerated lvr≡₁ lv≡₁))) =
    mkVoteGenerated lv≡v (inj₁ (mkVoteOldGenerated (trans lvr≤ lvr≡₁) (trans lv≡ lv≡₁)))
  glue-VoteNotGenerated-VoteGenerated (mkVoteNotGenerated lv≡ lvr≤) (mkVoteGenerated lv≡v (inj₂ (mkVoteNewGenerated lvr<₁ lvr≡₁))) =
    mkVoteGenerated lv≡v (inj₂ (mkVoteNewGenerated (≤-trans (s≤s (≡⇒≤ lvr≤)) lvr<₁) lvr≡₁))

  glue-VoteNotGenerated-VoteGeneratedNotSaved
    : ∀ {s₁ s₂ s₃} → VoteNotGenerated s₁ s₂ true → VoteGeneratedNotSaved s₂ s₃
      → VoteGeneratedNotSaved s₁ s₃
  glue-VoteNotGenerated-VoteGeneratedNotSaved vng (v , vg) =
    v , glue-VoteNotGenerated-VoteGenerated vng vg

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
      state          : StateTransProps.VoteGenerated pre post vote
    voteNew? = StateTransProps.isVoteNewGenerated pre post vote state
    field
      blockTriggered : VoteTriggeredByBlock vote block voteNew?

  record VoteGeneratedUnsavedCorrect (pre post : RoundManager) (block : Block) : Set where
    constructor mkVoteGeneratedUnsavedCorrect
    field
      vote           : Vote
      voteGenCorrect : VoteGeneratedCorrect pre post vote block

  glue-VoteGeneratedCorrect-VoteNotGenerated
    : ∀ {s₁ s₂ s₃ vote block}
      → VoteGeneratedCorrect s₁ s₂ vote block
      → StateTransProps.VoteNotGenerated s₂ s₃ true
      → VoteGeneratedCorrect s₁ s₃ vote block
  glue-VoteGeneratedCorrect-VoteNotGenerated vgc@(mkVoteGeneratedCorrect vg@(StateTransProps.mkVoteGenerated lv≡v (inj₁ oldVG)) blockTriggered) vng =
    mkVoteGeneratedCorrect (StateTransProps.glue-VoteGenerated-VoteNotGenerated vg vng) blockTriggered
  glue-VoteGeneratedCorrect-VoteNotGenerated vgc@(mkVoteGeneratedCorrect vg@(StateTransProps.mkVoteGenerated lv≡v (inj₂ newVG)) blockTriggered) vng =
    mkVoteGeneratedCorrect (StateTransProps.glue-VoteGenerated-VoteNotGenerated vg vng) blockTriggered

  glue-VoteNotGenerated-VoteGeneratedCorrect
    : ∀ {s₁ s₂ s₃ vote block}
      → StateTransProps.VoteNotGenerated s₁ s₂ true
      → VoteGeneratedCorrect s₂ s₃ vote block
      → VoteGeneratedCorrect s₁ s₃ vote block
  glue-VoteNotGenerated-VoteGeneratedCorrect vng (mkVoteGeneratedCorrect vg@(StateTransProps.mkVoteGenerated lv≡v (inj₁ oldVG)) blockTriggered) =
    mkVoteGeneratedCorrect (StateTransProps.glue-VoteNotGenerated-VoteGenerated vng vg) blockTriggered
  glue-VoteNotGenerated-VoteGeneratedCorrect vng (mkVoteGeneratedCorrect vg@(StateTransProps.mkVoteGenerated lv≡v (inj₂ newVG)) blockTriggered) =
    mkVoteGeneratedCorrect (StateTransProps.glue-VoteNotGenerated-VoteGenerated vng vg)
      blockTriggered

  glue-VoteNotGenerated-VoteGeneratedUnsavedCorrect
    : ∀ {s₁ s₂ s₃ block}
      → StateTransProps.VoteNotGenerated s₁ s₂ true
      → VoteGeneratedUnsavedCorrect s₂ s₃ block
      → VoteGeneratedUnsavedCorrect s₁ s₃ block
  glue-VoteNotGenerated-VoteGeneratedUnsavedCorrect vng (mkVoteGeneratedUnsavedCorrect vote voteGenCorrect) =
    mkVoteGeneratedUnsavedCorrect vote (glue-VoteNotGenerated-VoteGeneratedCorrect vng voteGenCorrect)

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
      nvg⊎vgusc    : StateTransProps.VoteNotGenerated pre post lvr≡? ⊎ VoteGeneratedUnsavedCorrect pre post block

  glue-VoteNotGenerated-VoteUnsentCorrect
    : ∀ {s₁ s₂ s₃ outs₁ outs₂ block lvr≡?}
      → StateTransProps.VoteNotGenerated s₁ s₂ true → OutputProps.NoVotes outs₁
      → VoteUnsentCorrect s₂ s₃ outs₂ block lvr≡?
      → VoteUnsentCorrect s₁ s₃ (outs₁ ++ outs₂) block lvr≡?
  glue-VoteNotGenerated-VoteUnsentCorrect{outs₁ = outs₁} vng₁ nvo (mkVoteUnsentCorrect noVoteMsgOuts (inj₁ vng₂)) =
    mkVoteUnsentCorrect (OutputProps.++-NoVotes outs₁ _ nvo noVoteMsgOuts) (inj₁ (StateTransProps.transVoteNotGenerated vng₁ vng₂))
  glue-VoteNotGenerated-VoteUnsentCorrect{outs₁ = outs₁} vng₁ nvo (mkVoteUnsentCorrect noVoteMsgOuts (inj₂ vgus)) =
    mkVoteUnsentCorrect ((OutputProps.++-NoVotes outs₁ _ nvo noVoteMsgOuts)) (inj₂ (glue-VoteNotGenerated-VoteGeneratedUnsavedCorrect vng₁ vgus))

  -- The handler correctly attempted to vote on `block`, assuming the safety
  -- data epoch matches the block epoch.
  VoteAttemptCorrect : (pre post : RoundManager) (outs : List Output) (block : Block) → Set
  VoteAttemptCorrect pre post outs block =
    (∃[ lvr≡? ] VoteUnsentCorrect pre post outs block lvr≡?) ⊎ VoteSentCorrect pre post outs block

  -- The voting process ended before `pssSafetyData-rm` could be updated
  voteAttemptBailed : ∀ {rm block} outs → OutputProps.NoVotes outs → VoteAttemptCorrect rm rm outs block
  voteAttemptBailed outs noVotesOuts = inj₁ (true , mkVoteUnsentCorrect noVotesOuts (inj₁ StateTransProps.reflVoteNotGenerated))

  glue-VoteNotGenerated-VoteAttemptCorrect
    : ∀ {s₁ s₂ s₃ outs₁ outs₂ block}
      → StateTransProps.VoteNotGenerated s₁ s₂ true → OutputProps.NoVotes outs₁
      → VoteAttemptCorrect s₂ s₃ outs₂ block
      → VoteAttemptCorrect s₁ s₃ (outs₁ ++ outs₂) block
  glue-VoteNotGenerated-VoteAttemptCorrect{outs₁ = outs₁} vng nvo (inj₁ (lvr≡? , vusCorrect)) =
    inj₁ (lvr≡? , glue-VoteNotGenerated-VoteUnsentCorrect{outs₁ = outs₁} vng nvo vusCorrect)
  glue-VoteNotGenerated-VoteAttemptCorrect{outs₁ = outs₁} vng nvo (inj₂ (mkVoteSentCorrect vm pid voteMsgOuts vgCorrect)) =
    inj₂ (mkVoteSentCorrect vm pid (OutputProps.++-NoVotes-OneVote outs₁ _ nvo voteMsgOuts) (glue-VoteNotGenerated-VoteGeneratedCorrect vng vgCorrect))

  VoteAttemptEpochReq : ∀ {pre post outs block} → VoteAttemptCorrect pre post outs block → Set
  VoteAttemptEpochReq (inj₁ (_ , mkVoteUnsentCorrect _ (inj₁ _))) =
    ⊤
  VoteAttemptEpochReq{pre}{block = block} (inj₁ (_ , mkVoteUnsentCorrect _ (inj₂ _))) =
    pre ^∙ pssSafetyData-rm ∙ sdEpoch ≡ (block ^∙ bEpoch)
  VoteAttemptEpochReq{pre}{block = block} (inj₂ _) =
    pre ^∙ pssSafetyData-rm ∙ sdEpoch ≡ (block ^∙ bEpoch)

  voteAttemptEpochReq!
    : ∀ {pre post outs block} → (vac : VoteAttemptCorrect pre post outs block)
      → pre ^∙ pssSafetyData-rm ∙ sdEpoch ≡ block ^∙ bEpoch → VoteAttemptEpochReq vac
  voteAttemptEpochReq! (inj₁ (_ , mkVoteUnsentCorrect _ (inj₁ _))) eq = tt
  voteAttemptEpochReq! (inj₁ (_ , mkVoteUnsentCorrect _ (inj₂ _))) eq = eq
  voteAttemptEpochReq! (inj₂ _) eq = eq

  record VoteAttemptCorrectWithEpochReq (pre post : RoundManager) (outs : List Output) (block : Block) : Set where
    constructor mkVoteAttemptCorrectWithEpochReq
    field
      voteAttempt : VoteAttemptCorrect pre post outs block
      sdEpoch≡?   : VoteAttemptEpochReq voteAttempt

  voteAttemptCorrectAndSent⇒voteSentCorrect : ∀ {pre post outs block vm}
                         → send (V vm) ∈ outputsToActions{pre} outs
                         → VoteAttemptCorrectWithEpochReq pre post outs block
                         → VoteSentCorrect                pre post outs block
  voteAttemptCorrectAndSent⇒voteSentCorrect{pre}{outs = outs} vm∈outs (mkVoteAttemptCorrectWithEpochReq (Left (_ , mkVoteUnsentCorrect noVoteMsgOuts _)) _) =
    ⊥-elim (sendVote∉actions{outs}{st = pre} (sym noVoteMsgOuts) vm∈outs)
  voteAttemptCorrectAndSent⇒voteSentCorrect{pre}{outs = outs}{vm = vm} vm∈outs (mkVoteAttemptCorrectWithEpochReq (Right vsc) _) = vsc

module QC where

  data _∈RoundManager_ (qc : QuorumCert) (rm : RoundManager) : Set where
    inHQC : qc ≡ rm ^∙ lBlockStore ∙ bsInner ∙ btHighestQuorumCert → qc ∈RoundManager rm
    inHCC : qc ≡ rm ^∙ lBlockStore ∙ bsInner ∙ btHighestCommitCert → qc ∈RoundManager rm
    -- NOTE: When `need/fetch` is implemented, we will need an additional
    -- constructor for sent qcs taken from the blockstore.

  OutputQc∈RoundManager : List Output → RoundManager → Set
  OutputQc∈RoundManager outs rm =
    All (λ out → ∀ qc nm → qc QC∈NM nm → nm Msg∈Out out → qc ∈RoundManager rm) outs

  SigForVote∈Qc∈Rm-SentB4 : Vote → PK → QuorumCert → RoundManager → SentMessages → Set
  SigForVote∈Qc∈Rm-SentB4 v pk qc rm pool =
    qc ∈RoundManager rm
    → WithVerSig pk v →
    ∀ {vs : Author × Signature} → let (pid , sig) = vs in
      vs ∈ qcVotes qc → rebuildVote qc vs ≈Vote v
    → MsgWithSig∈ pk sig pool
