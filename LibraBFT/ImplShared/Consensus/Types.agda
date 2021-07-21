{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap as KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
open import Data.String using (String)

-- This module defines types for an out-of-date implementation, based
-- on a previous version of LibraBFT.  It will be updated to model a
-- more recent version in future.
--
-- One important trick here is that the RoundManager type separayes
-- types that /define/ the EpochConfig and types that /use/ the
-- /EpochConfig/. The advantage of doing this separation can be seen
-- in Util.Util.liftEC, where we define a lifting of a function that
-- does not change the bits that define the EpochConfig into the whole
-- state.  This enables a more elegant approach for reasoning about
-- functions that do not change parts of the state responsible for
-- defining the epoch config.  However, the separation is not perfect,
-- so sometimes fields may be modified in EpochIndep even though there
-- is no epoch change.

module LibraBFT.ImplShared.Consensus.Types where
  open import LibraBFT.ImplShared.NetworkMsg                     public
  open import LibraBFT.ImplShared.Base.Types                     public
  open import LibraBFT.ImplShared.Consensus.Types.EpochIndep     public
  open import LibraBFT.ImplShared.Util.Crypto                    public

  data NewRoundReason : Set where
    QCReady : NewRoundReason
    TOReady : NewRoundReason

  record NewRoundEvent : Set where
    constructor NewRoundEvent∙new
    field
      _nreRound   : Round
      _nreReason  : NewRoundReason
    --  _nreTimeout : Duration
  unquoteDecl nreRound   nreReason = mkLens (quote NewRoundEvent)
             (nreRound ∷ nreReason ∷ [])

  record RoundState : Set where
    constructor RoundState∙new
    field
      -- ...
      _rsHighestCommittedRound : Round
      _rsCurrentRound          : Round
      _rsPendingVotes          : PendingVotes
      _rsVoteSent              : Maybe Vote
      -- ...
  open RoundState public
  unquoteDecl rsHighestCommittedRound   rsCurrentRound   rsPendingVotes
              rsVoteSent = mkLens (quote RoundState)
             (rsHighestCommittedRound ∷ rsCurrentRound ∷ rsPendingVotes ∷
              rsVoteSent ∷ [])

  -- The parts of the state of a peer that are used to
  -- define the EpochConfig are the SafetyRules and ValidatorVerifier:
  record RoundManager : Set where
    constructor RoundManager∙new
    field
      _rmEpochState       : EpochState
      _rmBlockStore       : BlockStore
      _rmRoundState       : RoundState
      _rmProposerElection : ProposerElection
      _rmSafetyRules      : SafetyRules
      _rmSyncOnly         : Bool
  open RoundManager public
  unquoteDecl rmEpochState   rmBlockStore   rmRoundState   rmProposerElection   rmSafetyRules   rmSyncOnly = mkLens (quote RoundManager)
             (rmEpochState ∷ rmBlockStore ∷ rmRoundState ∷ rmProposerElection ∷ rmSafetyRules ∷ rmSyncOnly ∷ [])

  rmEpoch : Lens RoundManager Epoch
  rmEpoch = rmEpochState ∙ esEpoch

  rmLastVotedRound : Lens RoundManager Round
  rmLastVotedRound = rmSafetyRules ∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound

  lProposerElection : Lens RoundManager ProposerElection
  lProposerElection = rmProposerElection

  lRoundState : Lens RoundManager RoundState
  lRoundState = rmRoundState

  rsVoteSent-rm : Lens RoundManager (Maybe Vote)
  rsVoteSent-rm = lRoundState ∙ rsVoteSent

  lSyncOnly : Lens RoundManager Bool
  lSyncOnly = rmSyncOnly

  lPendingVotes : Lens RoundManager PendingVotes
  lPendingVotes = rmRoundState ∙ rsPendingVotes

  lSafetyRules : Lens RoundManager SafetyRules
  lSafetyRules = rmSafetyRules

  lPersistentSafetyStorage : Lens RoundManager PersistentSafetyStorage
  lPersistentSafetyStorage = lSafetyRules ∙ srPersistentStorage

  lSafetyData : Lens RoundManager SafetyData
  lSafetyData = lPersistentSafetyStorage ∙ pssSafetyData

  lBlockStore : Lens RoundManager BlockStore
  lBlockStore = rmBlockStore

  lBlockTree : Lens RoundManager BlockTree
  lBlockTree = lBlockStore ∙ bsInner

  -- This is a trivial lens, which is used in the Haskell code, so we keep it here for consistency.
  lRoundManager : Lens RoundManager RoundManager
  lRoundManager = lens (λ _ _ f rm → f rm)

  srValidatorVerifier : Lens RoundManager ValidatorVerifier
  srValidatorVerifier = rmEpochState ∙ esVerifier


-- In some cases, the getting operation is not dependent but a lens still
  -- cannot be defined because the *setting* operation would require dependent
  -- types. Below, `rmGetValidatorVerifier` is an example of this situation, and
  -- we would "use" it like this
  --
  --    vv ← gets rmGetValidatorVerifier

  -- IMPL-DIFF : this is defined as a lens getter only (no setter) in Haskell.
  rmPgAuthor : RoundManager → Maybe Author
  rmPgAuthor rm =
    maybeS (rm ^∙ rmSafetyRules ∙ srValidatorSigner) nothing (just ∘ (_^∙ vsAuthor))

  -- NOTE: Use only for proofs.
  metaRMGetRealLastVotedRound : RoundManager → Round
  metaRMGetRealLastVotedRound = maybe (_^∙ vRound) 0 ∘ (_^∙ rmSafetyRules ∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVote)

  record GenesisInfo : Set where
    constructor mkGenInfo
    field
      -- TODO-1 : Nodes, PKs for initial epoch
      -- TODO-1 : Faults to tolerate (or quorum size?)
      genQC      : QuorumCert            -- We use the same genesis QC for both highestQC and
                                         -- highestCommitCert.
  open GenesisInfo

  postulate -- valid assumption
    -- We postulate the existence of GenesisInfo known to all
    -- TODO: construct one or write a function that generates one from some parameters.
    genesisInfo : GenesisInfo

  data ∈GenInfo-impl (gi : GenesisInfo) : Signature → Set where
   inGenQC : ∀ {vs} → vs ∈ qcVotes (genQC gi) → ∈GenInfo-impl gi (proj₂ vs)

  postulate -- TODO-1 : prove
    ∈GenInfo?-impl : (gi : GenesisInfo) (sig : Signature) → Dec (∈GenInfo-impl gi sig)

  postulate -- TODO-1: prove after defining genInfo
    genVotesRound≡0     : ∀ {pk v}
                       → (wvs : WithVerSig pk v)
                       → ∈GenInfo-impl genesisInfo (ver-signature wvs)
                       → v ^∙ vRound ≡ 0
    genVotesConsistent : (v1 v2 : Vote)
                       → ∈GenInfo-impl genesisInfo (_vSignature v1) → ∈GenInfo-impl genesisInfo (_vSignature v2)
                     → v1 ^∙ vProposedId ≡ v2 ^∙ vProposedId

  -- The Haskell implementation has many more constructors.
  -- Constructors are being added incrementally as needed for the verification effort.
  data ErrLog : Set where
    ErrBlockNotFound : HashValue   → ErrLog
    ErrVerify        : VerifyError → ErrLog

  -- To enable modeling of logging errors that have not been added yet,
  -- an inhabitant of ErrLog is postulated.
  postulate
    fakeErr : ErrLog

  -- To enable modeling of logging info that has not been added yet,
  -- InfoLog and an inhabitant is postulated.
  postulate
    InfoLog  : Set
    fakeInfo : InfoLog

