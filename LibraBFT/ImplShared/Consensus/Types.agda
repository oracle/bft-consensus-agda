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
  open import LibraBFT.ImplShared.Consensus.Types.EpochDep       public
  open import LibraBFT.ImplShared.Util.Crypto                    public

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
      _rmBlockStore       : BlockStore
      _rmRoundState       : RoundState
      _rmProposerElection : ProposerElection
      _rmSafetyRules      : SafetyRules
      _rmSyncOnly         : Bool
  open RoundManagerEC public
  unquoteDecl rmEpochState   rmBlockStore   rmRoundState   rmProposerElection   rmSafetyRules   rmSyncOnly = mkLens (quote RoundManagerEC)
             (rmEpochState ∷ rmBlockStore ∷ rmRoundState ∷ rmProposerElection ∷ rmSafetyRules ∷ rmSyncOnly ∷ [])

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

  -- Here I am thinking of defining various conditions sufficient to prove EpochConfigs are the same
  -- starting with a simple one, but other less and more specific ones may be useful too.
  data SameEpochCond (rmec1 rmec2 : RoundManagerEC) : Set where
   firstOne : rmec1 ^∙ rmEpochState ∙ esVerifier ≡ rmec2 ^∙ rmEpochState ∙ esVerifier
            → rmec1 ^∙ rmEpoch                   ≡ rmec2 ^∙ rmEpoch
            → SameEpochCond rmec1 rmec2

  RoundManagerEC-correct-≡ : (rmec1 : RoundManagerEC)
                           → (rmec2 : RoundManagerEC)
                           → SameEpochCond rmec1 rmec2
                           → RoundManagerEC-correct rmec1
                           → RoundManagerEC-correct rmec2
  RoundManagerEC-correct-≡ rmec1 rmec2 (firstOne refl refl) = id

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
           → (𝓔≡     : SameEpochCond rmec1 rmec2)
           → (rmec1-corr : RoundManagerEC-correct rmec1)
           → α-EC (rmec1 , rmec1-corr) ≡ α-EC (rmec2 , RoundManagerEC-correct-≡ rmec1 rmec2 𝓔≡  rmec1-corr)
  {-
  α-EC-≡ rmec1 rmec2 refl refl rmec1-corr = refl
  -}

  hasValidQCs : EpochConfig → BlockStore → Set
  hasValidQCs 𝓔 bs = ∀ {bid qc}
                     → (bid , qc) ∈ (kvm-toList (bs ^∙ bsInner ∙ btIdToQuorumCert))
                     → MetaIsValidQC 𝓔 qc

  hasValidQCs-subst : (𝓔₁ : EpochConfig) → (bs1 : BlockStore)
                    → (𝓔₂ : EpochConfig) → (bs2 : BlockStore)
                    → 𝓔₁ ≡ 𝓔₂
                    → bs1 ≡ bs2
                    → hasValidQCs 𝓔₁ bs1
                    → hasValidQCs 𝓔₂ bs2
  hasValidQCs-subst _ _ _ _ refl refl hvq = hvq

  record RoundManagerMetaWithEC (rmec : RoundManagerEC) (rmecc : RoundManagerEC-correct rmec) : Set where
    constructor RoundManagerWithEC∙new
    field
      _rmecMetaQCsValid : hasValidQCs (α-EC (rmec , rmecc)) (rmec ^∙ rmBlockStore)
  open RoundManagerMetaWithEC public
  -- Note: no lens because our lens support does not work for dependent types

  RoundManagerWithMetaEC-subst1 :  -- First a simple one that works for most cases (don't modify blockStore, don't change epoch config)
    ∀ (rmec1 rmec2 : RoundManagerEC)
    → (rmecc1  : RoundManagerEC-correct rmec1)
    → (rmecc2  : RoundManagerEC-correct rmec2)
    → RoundManagerMetaWithEC rmec1 rmecc1
    → α-EC (rmec1 , rmecc1) ≡ α-EC (rmec2 , rmecc2)
    → rmec1 ^∙ rmBlockStore ≡ rmec2 ^∙ rmBlockStore
    → RoundManagerMetaWithEC rmec2 rmecc2
  RoundManagerWithMetaEC-subst1 rmec1 rmec2 rmecc1 rmecc2 x₁ α≡ bs≡ =
    RoundManagerWithEC∙new (hasValidQCs-subst (α-EC (rmec1 , rmecc1)) (_rmBlockStore rmec1)
                                              (α-EC (rmec2 , rmecc2)) (_rmBlockStore rmec2)
                                                α≡ bs≡ (_rmecMetaQCsValid x₁))

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
      _rmMetaWithEC   : RoundManagerMetaWithEC _rmEC _rmEC-correct
     -- If we want to add pieces that neither contribute to the
     -- construction of the EC nor need one, they should be defined in
     -- RoundManager directly
  open RoundManager public

  -- TODO-2: We would need dependent lenses to have a lens from RoundManager to
  -- RoundManagerEC, since setting _rmEC means updating the proofs _rmEC-correct
  -- and _rmWithEC

  α-EC-RM : RoundManager → EpochConfig
  α-EC-RM rm = α-EC ((_rmEC rm) , (_rmEC-correct rm))


  record GoodLens {A} (l : Lens RoundManagerEC A) : Set where
    field
      getRM : ∀ (rm : RoundManager) (f : A → A)
            → Σ RoundManager (λ rm' → _rmEC rm' ≡ over l f (_rmEC rm))
  open GoodLens public

  GoodLens-∙ : ∀ {A B} (l : Lens RoundManagerEC A)
             → ⦃ gl : GoodLens l ⦄
             → (l' : Lens A B)
             → GoodLens (l ∙ l')
  GoodLens-∙ {A} {B} l ⦃ gl ⦄ l' =
    record { getRM = λ rm f → help rm f }
    where
      help : (rm : RoundManager) → (f : B → B)
           → Σ RoundManager (λ rm' → (rm' rmEC) ≡ over (l ∙ l') f (_rmEC rm))
      help rm f
         with getRM gl rm (_& l' %~ f)
      ... | rm' , prf = rm' , trans prf (over-∙ l l' f (_rmEC rm))

  -- These are the parts of the RoundManager that depend on an
  -- EpochConfig. We do not particularly care which EpochConfig
  -- they care about yet.
  --
  lBlockTree : Lens RoundManagerEC BlockTree
  lBlockTree = rmBlockStore ∙ bsInner


  rmSyncOnly-manual : Lens RoundManagerEC Bool
  rmSyncOnly-manual = mkLens' g s
    where
    g : RoundManagerEC → Bool
    g rmec = _rmSyncOnly rmec

    s : RoundManagerEC → Bool → RoundManagerEC
    s rmec b = record rmec { _rmSyncOnly = b}

  instance
     -- Note that this is an autogenerated lens that doesn't come anywhere near anything to do with
     -- epoch change, so is a good test example, though we can always define the top-level lenses
     -- manually if this doesn't work.  Maybe that's where I should start.

    rmSyncOnly-manual-good : GoodLens rmSyncOnly-manual
    rmSyncOnly-manual-good =
      record { getRM = λ rm f →
                 let rmec1 = _rmEC rm
                     rmec2 = over rmSyncOnly-manual f rmec1
                     𝓔s≡   = α-EC-≡ rmec1 rmec2 (firstOne refl refl) (_rmEC-correct rm)
                     rmec2corr = RoundManagerEC-correct-≡ rmec1 rmec2 (firstOne refl refl) (_rmEC-correct rm)
                 in (RoundManager∙new rmec2
                       rmec2corr
                       (RoundManagerWithMetaEC-subst1 rmec1 rmec2 (_rmEC-correct rm)
                                                      rmec2corr (_rmMetaWithEC rm) 𝓔s≡ refl))
                     , refl }

    rmSyncOnly' : Lens RoundManagerEC Bool
    rmSyncOnly' = rmSyncOnly

    rmSyncOnly-good : GoodLens rmSyncOnly'   -- We can similarly define an instance of GoodLens for an
                                     -- autogenerated Lens, but seems only if we rename it like
                                     -- this, not sure why.
    rmSyncOnly-good =
      record { getRM = λ rm f →
                 let rmec1 = _rmEC rm
                     rmec2 = over rmSyncOnly' f rmec1
                     𝓔s≡   = α-EC-≡ rmec1 rmec2 (firstOne refl refl) (_rmEC-correct rm)
                     rmec2corr = RoundManagerEC-correct-≡ rmec1 rmec2 (firstOne refl refl) (_rmEC-correct rm)
                 in (RoundManager∙new rmec2
                       rmec2corr
                       (RoundManagerWithMetaEC-subst1 rmec1 rmec2 (_rmEC-correct rm)
                                                      rmec2corr (_rmMetaWithEC rm) 𝓔s≡ refl))
                     , refl }

{- Hopefully these will become obsolete
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
-}
  -- NO-DEPENDENT-LENSES (don't change this without searching for other instances of it and treating
  -- them consistently).
  --
  -- Because our RoundManager is in three pieces to enable constructing an abstract EpochConfig in
  -- which parts of it depend, we would like to have something like:
  --
  --   Lens (rm : RoundManager) (BlockStore (α-EC-RM rm))
  --
  -- However, our rudimentary Lens support does not enable such dependent lenses.  Therefore, where
  -- the Haskell code we are modeling defines a Lens from RoundManager to BlockStore (called
  -- lBlockStore), enabling code like:
  --
  --   bs <- use lBlockStore
  --
  -- we instead define a function such as rmGetBlockStore below
  -- and "use" it like this:
  --
  --   s ← get
  --   let bs = rmGetBlockStore s


{- Hopefully these will become obsolete

  rmGetBlockStore : (rm : RoundManager) → BlockStore (α-EC-RM rm)
  rmGetBlockStore rm = (_rmWithEC rm) ^∙ (epBlockStore (α-EC-RM rm))

  rmSetBlockStore : (rm : RoundManager) → BlockStore (α-EC-RM rm) → RoundManager
  rmSetBlockStore rm bs = record rm { _rmWithEC = RoundManagerWithEC∙new bs }

  lBlockStore : ∀ {ec} → Lens (RoundManagerWithEC ec) (BlockStore ec)
  lBlockStore = epBlockStore _
-}

{-
  -- In some cases, the getting operation is not dependent but a lens still
  -- cannot be defined because the *setting* operation would require dependent
  -- types. Below, `rmGetValidatorVerifier` is an example of this situation, and
  -- we would "use" it like this
  --
  --    vv ← gets rmGetValidatorVerifier

  rmGetValidatorVerifier : RoundManager → ValidatorVerifier
  rmGetValidatorVerifier rm = _esVerifier (_rmEpochState (_rmEC rm))
-}

{- Hopefully these will become obsolete

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

  rsVoteSent-rm : Lens RoundManager (Maybe Vote)
  rsVoteSent-rm = lRoundState ∙ rsVoteSent

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

  -- IMPL-DIFF : this is defined as a lens getter only (no setter) in Haskell.
  rmPgAuthor : RoundManager → Maybe Author
  rmPgAuthor rm =
    maybeS (_rmEC rm ^∙ rmSafetyRules ∙ srValidatorSigner) nothing (just ∘ (_^∙ vsAuthor))

  lSafetyData : Lens RoundManager SafetyData
  lSafetyData = lPersistentSafetyStorage ∙ pssSafetyData
-}
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

  postulate -- TODO-2: define GenesisInfo to match implementation and write these functions
    initVV  : GenesisInfo → ValidatorVerifier
    init-EC : GenesisInfo → EpochConfig

  data ∈GenInfo-impl (gi : GenesisInfo) : Signature → Set where
   inGenQC : ∀ {vs} → vs ∈ qcVotes (genQC gi) → ∈GenInfo-impl gi (proj₂ vs)

  open import LibraBFT.Abstract.Records UID _≟UID_ NodeId
                                        (init-EC genesisInfo)
                                        (ConcreteVoteEvidence (init-EC genesisInfo))
                                        as Abs using ()

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
    ErrVerify : VerifyError → ErrLog

  -- To enable modeling of logging errors that have not been added yet,
  -- an inhabitant of ErrLog is postulated.
  postulate
    fakeErr : ErrLog

  -- To enable modeling of logging info that has not been added yet,
  -- InfoLog and an inhabitant is postulated.
  postulate
    InfoLog  : Set
    fakeInfo : InfoLog

