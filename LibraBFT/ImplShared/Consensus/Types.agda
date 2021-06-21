{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

{-# OPTIONS --allow-unsolved-metas #-}

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
  open import LibraBFT.ImplShared.Consensus.Types.MetaEpochIndep public
  open import LibraBFT.ImplShared.Consensus.Types.EpochDep       public

  open import LibraBFT.Abstract.Types.EpochConfig UID NodeId     public

  record EpochState : Set where
    constructor EpochState∙new
    field
      _esEpoch    : Epoch
      _esVerifier : ValidatorVerifier
  open EpochState public
  unquoteDecl esEpoch   esVerifier = mkLens (quote EpochState)
             (esEpoch ∷ esVerifier ∷ [])

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
  record RoundManagerEC : Set where
    constructor RoundManagerEC∙new
    field
      _rmEpochState       : EpochState
      _rmRoundState       : RoundState
      _rmProposerElection : ProposerElection
      _rmSafetyRules      : SafetyRules
      _rmSyncOnly         : Bool
  open RoundManagerEC public
  unquoteDecl rmEpochState   rmRoundState   rmProposerElection   rmSafetyRules   rmSyncOnly = mkLens (quote RoundManagerEC)
             (rmEpochState ∷ rmRoundState ∷ rmProposerElection ∷ rmSafetyRules ∷ rmSyncOnly ∷ [])

  rmEpoch : Lens RoundManagerEC Epoch
  rmEpoch = rmEpochState ∙ esEpoch

  rmLastVotedRound : Lens RoundManagerEC Round
  rmLastVotedRound = rmSafetyRules ∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound

  -- We need enough authors to withstand the desired number of
  -- byzantine failures.  We enforce this with a predicate over
  -- 'RoundManagerEC'.
  ValidatorVerifier-correct : ValidatorVerifier → Set
  ValidatorVerifier-correct vv =
    let numAuthors = kvm-size (vv ^∙ vvAddressToValidatorInfo)
        qsize      = vv ^∙ vvQuorumVotingPower
        bizF       = numAuthors ∸ qsize
     in suc (3 * bizF) ≤ numAuthors

  RoundManagerEC-correct : RoundManagerEC → Set
  RoundManagerEC-correct rmec = ValidatorVerifier-correct (rmec ^∙ rmEpochState ∙ esVerifier)

  RoundManagerEC-correct-≡ : (rmec1 : RoundManagerEC)
                             → (rmec2 : RoundManagerEC)
                             → (rmec1 ^∙ rmEpochState ∙ esVerifier) ≡ (rmec2 ^∙ rmEpochState ∙ esVerifier)
                             → RoundManagerEC-correct rmec1
                             → RoundManagerEC-correct rmec2
  RoundManagerEC-correct-≡ rmec1 rmec2 refl = id

  -- Given a well-formed set of definitions that defines an EpochConfig,
  -- α-EC will compute this EpochConfig by abstracting away the unecessary
  -- pieces from RoundManagerEC.
  -- TODO-2: update and complete when definitions are updated to more recent version
  α-EC : Σ RoundManagerEC RoundManagerEC-correct → EpochConfig
  α-EC (rmec , ok) =
    let numAuthors = kvm-size (rmec ^∙ rmEpochState ∙ esVerifier ∙ vvAddressToValidatorInfo)
        qsize      = rmec ^∙ rmEpochState ∙ esVerifier ∙ vvQuorumVotingPower
        bizF       = numAuthors ∸ qsize
     in (EpochConfig∙new {! someHash?!}
                (rmec ^∙ rmEpoch) numAuthors {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!})

  postulate
    α-EC-≡ : (rmec1  : RoundManagerEC)
           → (rmec2  : RoundManagerEC)
           → (vals≡  : rmec1 ^∙ rmEpochState ∙ esVerifier ≡ rmec2 ^∙ rmEpochState ∙ esVerifier)
           →           rmec1 ^∙ rmEpoch      ≡ rmec2 ^∙ rmEpoch
           → (rmec1-corr : RoundManagerEC-correct rmec1)
           → α-EC (rmec1 , rmec1-corr) ≡ α-EC (rmec2 , RoundManagerEC-correct-≡ rmec1 rmec2 vals≡ rmec1-corr)
  {-
  α-EC-≡ rmec1 rmec2 refl refl rmec1-corr = refl
  -}

  -- Finally, the RoundManager is split in two pieces: those that are used to make an EpochConfig
  -- versus those that use an EpochConfig.  The reason is that the *abstract* EpochConfig is a
  -- function of some parts of the RoundManager (_rmEC), and some parts depend on the abstract
  -- EpochConfig.  For example, _btIdToQuorumCert carries a proof that the QuorumCert is valid (for
  -- the abstract EpochConfig).
  record RoundManager : Set ℓ-RoundManager where
    constructor RoundManager∙new
    field
      _rmEC           : RoundManagerEC
      _rmEC-correct   : RoundManagerEC-correct _rmEC
      _rmWithEC       : RoundManagerWithEC (α-EC (_rmEC , _rmEC-correct))
     -- If we want to add pieces that neither contribute to the
     -- construction of the EC nor need one, they should be defined in
     -- RoundManager directly
  open RoundManager public

  -- TODO-2: We would need dependent lenses to have a lens from RoundManager to
  -- RoundManagerEC, since setting _rmEC means updating the proofs _rmEC-correct
  -- and _rmWithEC

  α-EC-RM : RoundManager → EpochConfig
  α-EC-RM rm = α-EC ((_rmEC rm) , (_rmEC-correct rm))

  rmGetEpochState : (rm : RoundManager) → EpochState
  rmGetEpochState rm = (_rmEC rm) ^∙ rmEpochState

  _rmHighestQC : (rm : RoundManager) → QuorumCert
  _rmHighestQC rm = _btHighestQuorumCert ((_rmWithEC rm) ^∙ (lBlockTree (α-EC-RM rm)))

  rmHighestQC : Lens RoundManager QuorumCert
  rmHighestQC = mkLens' _rmHighestQC
                        (λ (RoundManager∙new ec ecc (RoundManagerWithEC∙new (BlockStore∙new bsInner'))) qc
                          → RoundManager∙new ec ecc (RoundManagerWithEC∙new (BlockStore∙new (record bsInner' {_btHighestQuorumCert = qc}))))

  _rmHighestCommitQC : (rm : RoundManager) → QuorumCert
  _rmHighestCommitQC rm = _btHighestCommitCert ((_rmWithEC rm) ^∙ (lBlockTree (α-EC-RM rm)))

  rmHighestCommitQC : Lens RoundManager QuorumCert
  rmHighestCommitQC = mkLens' _rmHighestCommitQC
                        (λ (RoundManager∙new ec ecc (RoundManagerWithEC∙new (BlockStore∙new bsInner'))) qc
                          → RoundManager∙new ec ecc (RoundManagerWithEC∙new (BlockStore∙new (record bsInner' {_btHighestCommitCert = qc}))))

  -- TODO-1? We would need lenses to be dependent to make a lens from round
  -- managers to block stores.
  rmGetBlockStore : (rm : RoundManager) → BlockStore (α-EC-RM rm)
  rmGetBlockStore rm = (_rmWithEC rm) ^∙ (epBlockStore (α-EC-RM rm))

  rmSetBlockStore : (rm : RoundManager) → BlockStore (α-EC-RM rm) → RoundManager
  rmSetBlockStore rm bs = record rm { _rmWithEC = RoundManagerWithEC∙new bs }

  rmGetValidatorVerifier : RoundManager → ValidatorVerifier
  rmGetValidatorVerifier rm = _esVerifier (_rmEpochState (_rmEC rm))

  lProposerElection : Lens RoundManager ProposerElection
  lProposerElection = mkLens' g s
    where
    g : RoundManager → ProposerElection
    g rm = _rmEC rm ^∙ rmProposerElection

    s : RoundManager → ProposerElection → RoundManager
    s rm pe = record rm { _rmEC = (_rmEC rm) & rmProposerElection ∙~ pe }

  lRoundState : Lens RoundManager RoundState
  lRoundState = mkLens' g s
    where
    g : RoundManager → RoundState
    g rm = _rmEC rm ^∙ rmRoundState

    s : RoundManager → RoundState → RoundManager
    s rm rs = record rm { _rmEC = (_rmEC rm) & rmRoundState ∙~ rs }

  lSyncOnly : Lens RoundManager Bool
  lSyncOnly = mkLens' g s
    where
    g : RoundManager → Bool
    g rm = _rmEC rm ^∙ rmSyncOnly

    s : RoundManager → Bool → RoundManager
    s rm so = record rm { _rmEC = (_rmEC rm) & rmSyncOnly ∙~ so }

  lPendingVotes : Lens RoundManager PendingVotes
  lPendingVotes = mkLens' g s
    where
    g : RoundManager → PendingVotes
    g rm = _rmEC rm ^∙ (rmRoundState ∙ rsPendingVotes)

    s : RoundManager → PendingVotes → RoundManager
    s rm pv = record rm { _rmEC = (_rmEC rm) & rmRoundState ∙ rsPendingVotes ∙~ pv }

  lSafetyRules : Lens RoundManager SafetyRules
  lSafetyRules = mkLens' g s
    where
    g : RoundManager → SafetyRules
    g rm = _rmEC rm ^∙ rmSafetyRules

    s : RoundManager → SafetyRules → RoundManager
    s rm sr = record rm { _rmEC = (_rmEC rm) & rmSafetyRules ∙~ sr }

  lPersistentSafetyStorage : Lens RoundManager PersistentSafetyStorage
  lPersistentSafetyStorage = lSafetyRules ∙ srPersistentStorage

  lSafetyData : Lens RoundManager SafetyData
  lSafetyData = lPersistentSafetyStorage ∙ pssSafetyData

  -- These are placeholders so that we can model error and logging outputs even
  -- though we don't yet model them in detail.
  postulate
    FakeInfo FakeErr : Set
    fakeErr          : FakeErr
    fakeInfo         : FakeInfo

  data Output : Set where
    BroadcastProposal : ProposalMsg                   → Output
    LogErr            : FakeErr                       → Output
    LogInfo           : FakeInfo                      → Output
    SendVote          : VoteMsg → List Author → Output
  open Output public

  SendVote-inj-v : ∀ {x1 x2 y1 y2} → SendVote x1 y1 ≡ SendVote x2 y2 → x1 ≡ x2
  SendVote-inj-v refl = refl

  SendVote-inj-si : ∀ {x1 x2 y1 y2} → SendVote x1 y1 ≡ SendVote x2 y2 → y1 ≡ y2
  SendVote-inj-si refl = refl

  IsSendVote : Output → Set
  IsSendVote out = ∃₂ λ mv pid → out ≡ SendVote mv pid

  isSendVote? : (out : Output) → Dec (IsSendVote out)
  isSendVote? (BroadcastProposal _) = no λ ()
  isSendVote? (LogErr _)            = no λ ()
  isSendVote? (LogInfo _)           = no λ ()
  isSendVote? (SendVote mv pid)     = yes (mv , pid , refl)

  SendVote∉Output : ∀ {vm pid outs} → List-filter isSendVote? outs ≡ [] → ¬ (SendVote vm pid ∈ outs)
  SendVote∉Output () (here refl)
  SendVote∉Output{outs = x ∷ outs'} eq (there vm∈outs)
     with isSendVote? x
  ... | no proof = SendVote∉Output eq vm∈outs
