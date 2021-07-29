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
      _rmProposalGenerator : ProposalGenerator
      _rmSafetyRules      : SafetyRules
      _rmSyncOnly         : Bool
  open RoundManager public
  unquoteDecl rmEpochState   rmBlockStore   rmRoundState   rmProposerElection
              rmProposalGenerator   rmSafetyRules   rmSyncOnly = mkLens (quote RoundManager)
             (rmEpochState ∷ rmBlockStore ∷ rmRoundState ∷ rmProposerElection ∷
              rmProposalGenerator ∷ rmSafetyRules ∷ rmSyncOnly ∷ [])

  -- IMPL-DIFF: this is RoundManager field/lens in Haskell; and it is implemented completely different
  rmObmAllAuthors : Lens RoundManager (List Author)
  rmObmAllAuthors = mkLens'
    (λ rm → List-map proj₁ (kvm-toList (rm ^∙ rmEpochState ∙ esVerifier ∙ vvAddressToValidatorInfo)))
    (λ rm _ → rm) -- TODO-1 cannot be written

  lRoundManager : Lens RoundManager RoundManager
  lRoundManager = lens (λ _ _ f rm → f rm)

  lBlockStore : Lens RoundManager BlockStore
  lBlockStore = rmBlockStore

  lBlockTree : Lens RoundManager BlockTree
  lBlockTree = lBlockStore ∙ bsInner

  lPendingVotes : Lens RoundManager PendingVotes
  lPendingVotes = rmRoundState ∙ rsPendingVotes

  lRoundState : Lens RoundManager RoundState
  lRoundState = rmRoundState

  lProposerElection : Lens RoundManager ProposerElection
  lProposerElection = rmProposerElection

  lProposalGenerator : Lens RoundManager ProposalGenerator
  lProposalGenerator = rmProposalGenerator

  lSafetyRules : Lens RoundManager SafetyRules
  lSafetyRules = rmSafetyRules

  lPersistentSafetyStorage : Lens RoundManager PersistentSafetyStorage
  lPersistentSafetyStorage = lSafetyRules ∙ srPersistentStorage

  -- getter only in Haskell
  pgAuthor : Lens RoundManager (Maybe Author)
  pgAuthor = mkLens' g s
    where
    g : RoundManager → Maybe Author
    g rm = maybeS (rm ^∙ rmSafetyRules ∙ srValidatorSigner) nothing (just ∘ (_^∙ vsAuthor))
    s : RoundManager → Maybe Author → RoundManager
    s rm _ma = rm -- TODO-1 cannot be written

  -- getter only in Haskell
  srValidatorVerifier : Lens RoundManager ValidatorVerifier
  srValidatorVerifier = rmEpochState ∙ esVerifier

  -- getter only in Haskell
  -- IMPL-DIFF : this returns Author OR does an errorExit
  rmObmMe : Lens RoundManager (Maybe Author)
  rmObmMe = mkLens' g s
    where
    g : RoundManager → Maybe Author
    g rm = case rm ^∙ rmSafetyRules ∙ srValidatorSigner of λ where
             (just vs) → just (vs ^∙ vsAuthor)
             nothing   → nothing
    s : RoundManager → Maybe Author → RoundManager
    s s _ = s

  -- getter only in Haskell
  rmEpoch : Lens RoundManager Epoch
  rmEpoch = rmEpochState ∙ esEpoch

  -- not defined in Haskell
  rmLastVotedRound : Lens RoundManager Round
  rmLastVotedRound = rmSafetyRules ∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound

  -- BEGIN : lens mimicking Haskell/LBFT RW* setters.
  -- IN THE MODEL OF THE HASKELL CODE, THESE SHOULD ONLY BE USED FOR SETTING.
  -- THEY CAN BE USED AS GETTERS IN PROPERTIES/PROOFS.
  rsVoteSent-rm : Lens RoundManager (Maybe Vote)
  rsVoteSent-rm = lRoundState ∙ rsVoteSent

  pssSafetyData-rm : Lens RoundManager SafetyData
  pssSafetyData-rm = lPersistentSafetyStorage ∙ pssSafetyData
  -- END : lens mimicking Haskell/LBFT RW* setters.

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

