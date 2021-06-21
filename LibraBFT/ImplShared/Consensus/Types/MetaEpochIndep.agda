{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Data.String using (String)
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.Prelude
open import Optics.All

{- Defines meta-level instrumentation for epoch-independent types in order to
-- reason about the implementation.
-}
module LibraBFT.ImplShared.Consensus.Types.MetaEpochIndep where

-- Meta-level instrumentation for reasoning about the source of a vote.
data MetaVoteSrc : Set where
  mvsNew mvsLastVote : MetaVoteSrc

record VoteWithMeta : Set where
  constructor VoteWithMeta∙new
  field
    _mvVote : Vote
    _mvSrc  : MetaVoteSrc
open Vote public
unquoteDecl mvVote mvSrc =
  mkLens (quote VoteWithMeta) (mvVote ∷ mvSrc ∷ [])

unmetaVote : VoteWithMeta → Vote
unmetaVote mv = mv ^∙ mvVote

record VoteMsgWithMeta : Set where
  constructor VoteMsgWithMeta∙new
  field
    _mvmVoteMsg  : VoteMsg
    _mvmSrc      : MetaVoteSrc
unquoteDecl mvmVoteMsg   mvmSrc = mkLens (quote VoteMsgWithMeta)
           (mvmVoteMsg ∷ mvmSrc ∷ [])

VoteMsgWithMeta∙fromVoteWithMeta : VoteWithMeta → SyncInfo → VoteMsgWithMeta
VoteMsgWithMeta∙fromVoteWithMeta mv si = VoteMsgWithMeta∙new (VoteMsg∙new (unmetaVote mv) si) (mv ^∙ mvSrc)

unmetaVoteMsg : VoteMsgWithMeta → VoteMsg
unmetaVoteMsg = _^∙ mvmVoteMsg

mvmVoteWithMeta : Lens VoteMsgWithMeta VoteWithMeta
mvmVoteWithMeta = mkLens' g s
  where
  g : VoteMsgWithMeta → VoteWithMeta
  g vm = VoteWithMeta∙new (vm ^∙ mvmVoteMsg ∙ vmVote) (vm ^∙ mvmSrc)

  s : VoteMsgWithMeta → VoteWithMeta → VoteMsgWithMeta
  s vm v = VoteMsgWithMeta∙new ((vm ^∙ mvmVoteMsg) & vmVote ∙~ v ^∙ mvVote) (v ^∙ mvSrc)
