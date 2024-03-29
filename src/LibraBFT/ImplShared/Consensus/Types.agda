{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import Optics.All
open import Util.Encode
open import Util.KVMap             as KVMap
open import Util.PKCS
open import Util.Prelude
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

  record ExponentialTimeInterval : Set where
    constructor mkExponentialTimeInterval
    field
      _etiBaseMs       : U64
      _etiExponentBase : F64
      _etiMaxExponent  : Usize
  unquoteDecl etiBaseMs   etiExponentBase   etiMaxExponent  = mkLens (quote ExponentialTimeInterval)
             (etiBaseMs ∷ etiExponentBase ∷ etiMaxExponent ∷ [])

  RoundStateTimeInterval = ExponentialTimeInterval

  record RoundState : Set where
    constructor mkRoundState
    field
      _rsTimeInterval          : RoundStateTimeInterval
      _rsHighestCommittedRound : Round
      _rsCurrentRound          : Round
      _rsCurrentRoundDeadline  : Instant
      _rsPendingVotes          : PendingVotes
      _rsVoteSent              : Maybe Vote
  open RoundState public
  unquoteDecl rsTimeInterval           rsHighestCommittedRound   rsCurrentRound
              rsCurrentRoundDeadline   rsPendingVotes            rsVoteSent = mkLens (quote RoundState)
             (rsTimeInterval         ∷ rsHighestCommittedRound ∷ rsCurrentRound ∷
              rsCurrentRoundDeadline ∷ rsPendingVotes          ∷ rsVoteSent ∷ [])

  record ObmNeedFetch : Set where
    constructor ObmNeedFetch∙new

  -- The parts of the state of a peer that are used to
  -- define the EpochConfig are the SafetyRules and ValidatorVerifier:
  record RoundManager : Set where
    constructor RoundManager∙new
    field
      _rmObmNeedFetch     : ObmNeedFetch
      -------------------------
      _rmEpochState       : EpochState
      _rmBlockStore       : BlockStore
      _rmRoundState       : RoundState
      _rmProposerElection : ProposerElection
      _rmProposalGenerator : ProposalGenerator
      _rmSafetyRules      : SafetyRules
      _rmSyncOnly         : Bool
  open RoundManager public
  unquoteDecl rmObmNeedFetch
              rmEpochState   rmBlockStore   rmRoundState   rmProposerElection
              rmProposalGenerator   rmSafetyRules   rmSyncOnly = mkLens (quote RoundManager)
             (rmObmNeedFetch ∷
              rmEpochState ∷ rmBlockStore ∷ rmRoundState ∷ rmProposerElection ∷
              rmProposalGenerator ∷ rmSafetyRules ∷ rmSyncOnly ∷ [])

  -- IMPL-DIFF: this is RoundManager field/lens in Haskell; and it is implemented completely different
  rmObmAllAuthors : Lens RoundManager (List Author)
  rmObmAllAuthors = mkLens'
    (λ rm → List-map proj₁ (kvm-toList (rm ^∙ rmEpochState ∙ esVerifier ∙ vvAddressToValidatorInfo)))
    (λ rm _ → rm) -- TODO-1 cannot be written

  -- IMPL-DIFF : In places that do "set"
  -- e.g., RoundState.processCertificates
  -- the Haskell code is :               rsVoteSent     .= Nothing
  -- the Agda    code is : lRoundState ∙ rsVoteSent     ∙= nothing
  --
  -- The Haskell code leverages the "RW" constraints (e.g., RWRoundState)
  -- to enable not specifying where something is contained (i.e., in the round manager).
  -- The Agda code does not model that, therefore it needs `lRoundState`.

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

  lObmNeedFetch : Lens RoundManager ObmNeedFetch
  lObmNeedFetch = rmObmNeedFetch

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

  -- not defined in Haskell, only used for proofs
  rmValidatorVerifer : Lens RoundManager ValidatorVerifier
  rmValidatorVerifer = rmEpochState ∙ esVerifier

  -- getter only in Haskell
  rmRound : Lens RoundManager Round
  rmRound = rmRoundState ∙ rsCurrentRound

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

  record BootstrapInfo : Set where
    constructor mkBootstrapInfo
    field
      _bsiNumFaults : ℕ
      _bsiLIWS      : LedgerInfoWithSignatures
      _bsiVSS       : List ValidatorSigner
      _bsiVV        : ValidatorVerifier
      _bsiPE        : ProposerElection

  open BootstrapInfo public
  unquoteDecl bsiNumFaults   bsiLIWS   bsiVSS   bsiVV   bsiPE = mkLens (quote BootstrapInfo)
             (bsiNumFaults ∷ bsiLIWS ∷ bsiVSS ∷ bsiVV ∷ bsiPE ∷ [])

  postulate -- valid assumption
    -- We postulate the existence of BootstrapInfo known to all
    -- TODO: construct one or write a function that generates one from some parameters.
    fakeBootstrapInfo : BootstrapInfo

  data ∈BootstrapInfo-impl (bi : BootstrapInfo) : Signature → Set where
   inBootstrapQC : ∀ {sig} → sig ∈ (KVMap.elems (bi ^∙ bsiLIWS ∙ liwsSignatures))
                 → ∈BootstrapInfo-impl bi sig

  postulate -- TODO-1 : prove
    ∈BootstrapInfo?-impl : (bi : BootstrapInfo) (sig : Signature)
                         → Dec (∈BootstrapInfo-impl bi sig)

  postulate -- TODO-1: prove after defining bootstrapInfo
    bootstrapVotesRound≡0
      : ∀ {pk v}
      → (wvs : WithVerSig pk v)
      → ∈BootstrapInfo-impl fakeBootstrapInfo (ver-signature wvs)
      → v ^∙ vRound ≡ 0
    bootstrapVotesConsistent
      : (v1 v2 : Vote)
      → ∈BootstrapInfo-impl fakeBootstrapInfo (_vSignature v1)
      → ∈BootstrapInfo-impl fakeBootstrapInfo (_vSignature v2)
      → v1 ^∙ vProposedId ≡ v2 ^∙ vProposedId

  -- To enable modeling of logging info that has not been added yet,
  -- InfoLog and an inhabitant is postulated.
  postulate -- Valid assumption: InfoLog type
    InfoLog  : Set
    fakeInfo : InfoLog

  -- The Haskell implementation has many more constructors.
  -- Constructors are being added incrementally as needed for the verification effort.
  data ErrLog : Set where
    -- full name of following field : Consensus_BlockNotFound
    ErrCBlockNotFound   : HashValue   → ErrLog
    -- full name of following field : ExecutionCorrectnessClient_BlockNotFound
    ErrECCBlockNotFound : HashValue   → ErrLog
    ErrInfo             : InfoLog     → ErrLog -- to exit early, but not an error
    ErrVerify           : VerifyError → ErrLog

  -- To enable modeling of logging errors that have not been added yet,
  -- an inhabitant of ErrLog is postulated.
  postulate -- Valid assumption: ErrLog type
    fakeErr : ErrLog

  record TxTypeDependentStuffForNetwork : Set where
    constructor TxTypeDependentStuffForNetwork∙new
    field
      _ttdsnProposalGenerator : ProposalGenerator
      _ttdsnStateComputer     : StateComputer
  open TxTypeDependentStuffForNetwork public
  unquoteDecl ttdsnProposalGenerator   ttdsnStateComputer = mkLens (quote TxTypeDependentStuffForNetwork)
             (ttdsnProposalGenerator ∷ ttdsnStateComputer ∷ [])
