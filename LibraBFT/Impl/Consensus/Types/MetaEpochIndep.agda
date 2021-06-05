{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Impl.Consensus.Types.EpochIndep

open import Data.String using (String)

{- Defines meta-level instrumentation for epoch-independent types in order to
-- reason about the implementation.
-}
module LibraBFT.Impl.Consensus.Types.MetaEpochIndep where

  -- Meta-level instrumentation for reasoning about the source of a vote.
data MetaVoteSrc : Set where
  mvsNew mvsLastVote : MetaVoteSrc

record MetaVote : Set where
  constructor MetaVote∙new
  field
    ₋mvVote : Vote
    ₋mvSrc  : MetaVoteSrc
open Vote public
unquoteDecl mvVote mvSrc =
  mkLens (quote MetaVote) (mvVote ∷ mvSrc ∷ [])

unmetaVote : MetaVote → Vote
unmetaVote mv = mv ^∙ mvVote

record MetaVoteMsg : Set where
  constructor MetaVoteMsg∙new
  field
    ₋mvmVote     : MetaVote
    ₋mvmSyncInfo : SyncInfo
unquoteDecl mvmVote   mvmSyncInfo = mkLens (quote MetaVoteMsg)
            (mvmVote ∷ mvmSyncInfo ∷ [])

mvmSrc : Lens MetaVoteMsg MetaVoteSrc
mvmSrc = mvmVote ∙ mvSrc

unmetaVoteMsg : MetaVoteMsg → VoteMsg
unmetaVoteMsg mvm = VoteMsg∙new (unmetaVote (mvm ^∙ mvmVote)) (mvm ^∙ mvmSyncInfo)

data Output : Set where
  BroadcastProposal : ProposalMsg               → Output
  LogErr            : String                    → Output
  -- LogInfo           : InfoLog a              → Output
  SendVote          : MetaVoteMsg → List Author → Output
open Output public

SendVote-inj-v : ∀ {x1 x2 y1 y2} → SendVote x1 y1 ≡ SendVote x2 y2 → x1 ≡ x2
SendVote-inj-v refl = refl

SendVote-inj-si : ∀ {x1 x2 y1 y2} → SendVote x1 y1 ≡ SendVote x2 y2 → y1 ≡ y2
SendVote-inj-si refl = refl
