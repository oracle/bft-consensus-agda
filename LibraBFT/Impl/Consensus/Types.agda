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

module LibraBFT.Impl.Consensus.Types where
  open import LibraBFT.Impl.Base.Types                       public
  open import LibraBFT.Impl.NetworkMsg                       public
  open import LibraBFT.Abstract.Types.EpochConfig UID NodeId public
  open import LibraBFT.Impl.Consensus.Types.EpochIndep       public
  open import LibraBFT.Impl.Consensus.Types.EpochDep         public

  record EpochState : Set where
    constructor EpochState∙new
    field
      ₋esEpoch    : Epoch
      ₋esVerifier : ValidatorVerifier
  open EpochState public
  unquoteDecl esEpoch   esVerifier = mkLens (quote EpochState)
             (esEpoch ∷ esVerifier ∷ [])

  data NewRoundReason : Set where
    QCReady : NewRoundReason
    TOReady : NewRoundReason

  record NewRoundEvent : Set where
    constructor NewRoundEvent∙new
    field
      ₋nreRound   : Round
      ₋nreReason  : NewRoundReason
    --  ₋nreTimeout : Duration
  unquoteDecl nreRound   nreReason = mkLens (quote NewRoundEvent)
             (nreRound ∷ nreReason ∷ [])

  record RoundState : Set where
    constructor RoundState∙new
    field
      -- ...
      ₋rsHighestCommittedRound : Round
      ₋rsCurrentRound          : Round
      ₋rsPendingVotes          : PendingVotes
      ₋rsVoteSent              : Maybe Vote
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
      ₋rmEpochState       : EpochState
      ₋rmRoundState       : RoundState
      ₋rmProposerElection : ProposerElection
      ₋rmSafetyRules      : SafetyRules
      ₋rmSyncOnly         : Bool
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
  -- function of some parts of the RoundManager (₋rmEC), and some parts depend on the abstract
  -- EpochConfig.  For example, ₋btIdToQuorumCert carries a proof that the QuorumCert is valid (for
  -- the abstract EpochConfig).
  record RoundManager : Set ℓ-RoundManager where
    constructor RoundManager∙new
    field
      ₋rmEC           : RoundManagerEC
      ₋rmEC-correct   : RoundManagerEC-correct ₋rmEC
      ₋rmWithEC       : RoundManagerWithEC (α-EC (₋rmEC , ₋rmEC-correct))
     -- If we want to add pieces that neither contribute to the
     -- construction of the EC nor need one, they should be defined in
     -- RoundManager directly
  open RoundManager public

  α-EC-RM : RoundManager → EpochConfig
  α-EC-RM rm = α-EC ((₋rmEC rm) , (₋rmEC-correct rm))

  rmGetEpochState : (rm : RoundManager) → EpochState
  rmGetEpochState rm = (₋rmEC rm) ^∙ rmEpochState

  lValidatorVerifier : Lens RoundManager ValidatorVerifier
  lValidatorVerifier = mkLens' g s
   where
    g : RoundManager → ValidatorVerifier
    g rm = ₋rmEC rm  ^∙ (rmEpochState ∙ esVerifier)
    s : RoundManager → ValidatorVerifier → RoundManager
    s rm v = -- IMPL TODO : not sure if we need this anymore
      let es = record (rmGetEpochState rm) { ₋esVerifier = v }
          r  = record rm { ₋rmEC = (₋rmEC rm)
                           [ rmEpochState := {!!}
                           ]
                         }
       in r

  ₋rmHighestQC : (rm : RoundManager) → QuorumCert
  ₋rmHighestQC rm = ₋btHighestQuorumCert ((₋rmWithEC rm) ^∙ (lBlockTree (α-EC-RM rm)))

  rmHighestQC : Lens RoundManager QuorumCert
  rmHighestQC = mkLens' ₋rmHighestQC
                        (λ (RoundManager∙new ec ecc (RoundManagerWithEC∙new (BlockStore∙new bsInner))) qc
                          → RoundManager∙new ec ecc (RoundManagerWithEC∙new (BlockStore∙new (record bsInner {₋btHighestQuorumCert = qc}))))

  ₋rmHighestCommitQC : (rm : RoundManager) → QuorumCert
  ₋rmHighestCommitQC rm = ₋btHighestCommitCert ((₋rmWithEC rm) ^∙ (lBlockTree (α-EC-RM rm)))

  rmHighestCommitQC : Lens RoundManager QuorumCert
  rmHighestCommitQC = mkLens' ₋rmHighestCommitQC
                        (λ (RoundManager∙new ec ecc (RoundManagerWithEC∙new (BlockStore∙new bsInner))) qc
                          → RoundManager∙new ec ecc (RoundManagerWithEC∙new (BlockStore∙new (record bsInner {₋btHighestCommitCert = qc}))))

  -- TODO-1? We would need lenses to be dependent to make a lens from round
  -- managers to block stores.

  rmGetBlockStore : (rm : RoundManager) → BlockStore (α-EC-RM rm)
  rmGetBlockStore rm = (₋rmWithEC rm) ^∙ (epBlockStore (α-EC-RM rm))

  rmGetValidatorVerifier : RoundManager → ValidatorVerifier
  rmGetValidatorVerifier rm = ₋esVerifier (₋rmEpochState (₋rmEC rm))

  lProposerElection : Lens RoundManager ProposerElection
  lProposerElection = mkLens' g s
    where
    g : RoundManager → ProposerElection
    g rm = ₋rmEC rm ^∙ rmProposerElection

    s : RoundManager → ProposerElection → RoundManager
    s rm pe = record rm { ₋rmEC = (₋rmEC rm) [ rmProposerElection := pe ] }

  lRoundState : Lens RoundManager RoundState
  lRoundState = mkLens' g s
    where
    g : RoundManager → RoundState
    g rm = ₋rmEC rm ^∙ rmRoundState

    s : RoundManager → RoundState → RoundManager
    s rm rs = record rm { ₋rmEC = (₋rmEC rm) [ rmRoundState := rs ]  }

  lSyncOnly : Lens RoundManager Bool
  lSyncOnly = mkLens' g s
    where
    g : RoundManager → Bool
    g rm = ₋rmEC rm ^∙ rmSyncOnly

    s : RoundManager → Bool → RoundManager
    s rm so = record rm { ₋rmEC = (₋rmEC rm) [ rmSyncOnly := so ] }

  lPendingVotes : Lens RoundManager PendingVotes
  lPendingVotes = mkLens' g s
    where
    g : RoundManager → PendingVotes
    g rm = ₋rmEC rm ^∙ (rmRoundState ∙ rsPendingVotes)

    s : RoundManager → PendingVotes → RoundManager
    s rm pv = record rm { ₋rmEC = (₋rmEC rm) [ rmRoundState ∙ rsPendingVotes := pv ]  }

  lSafetyRules : Lens RoundManager SafetyRules
  lSafetyRules = mkLens' g s
    where
    g : RoundManager → SafetyRules
    g rm = ₋rmEC rm ^∙ rmSafetyRules

    s : RoundManager → SafetyRules → RoundManager
    s rm sr = record rm { ₋rmEC = (₋rmEC rm) [ rmSafetyRules := sr ]}

  lPersistentSafetyStorage : Lens RoundManager PersistentSafetyStorage
  lPersistentSafetyStorage = lSafetyRules ∙ srPersistentStorage

  lSafetyData : Lens RoundManager SafetyData
  lSafetyData = lPersistentSafetyStorage ∙ pssSafetyData
