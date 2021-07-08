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

  RoundManagerEC-correct-≡1 : (rmec1 : RoundManagerEC)
                            → (rmec2 : RoundManagerEC)
                            → (rmec1 ^∙ rmEpochState ∙ esVerifier) ≡ (rmec2 ^∙ rmEpochState ∙ esVerifier)
                            → RoundManagerEC-correct rmec1
                            → RoundManagerEC-correct rmec2
  RoundManagerEC-correct-≡1 rmec1 rmec2 refl = id

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
                    → bs1 ^∙ bsInner ∙ btIdToQuorumCert ≡ bs2 ^∙ bsInner ∙ btIdToQuorumCert
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
    → rmec1 ^∙ rmBlockStore ∙ bsInner ∙ btIdToQuorumCert ≡ rmec2 ^∙ rmBlockStore ∙ bsInner ∙ btIdToQuorumCert
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

  record RMLens {A} (l : Lens RoundManagerEC A) : Set where
    field
      getRM : ∀ (rm : RoundManager) (f : A → A)
            → Σ RoundManager (λ rm' → _rmEC rm' ≡ over l f (_rmEC rm))
  open RMLens public

  -- These are the parts of the RoundManager that depend on an
  -- EpochConfig. We do not particularly care which EpochConfig
  -- they care about yet.
  --
  lBlockTree : Lens RoundManagerEC BlockTree
  lBlockTree = rmBlockStore ∙ bsInner

  -- We need different names than the autogenerated lenses, otherwise Agda can't parse the instance
  -- declarations below.
  rmEpochState'       : Lens RoundManagerEC EpochState
  rmEpochState'       = rmEpochState
  rmBlockStore'       : Lens RoundManagerEC BlockStore
  rmBlockStore'       = rmBlockStore
  rmRoundState'       : Lens RoundManagerEC RoundState
  rmRoundState'       = rmRoundState
  rmProposerElection' : Lens RoundManagerEC ProposerElection
  rmProposerElection' = rmProposerElection
  rmSafetyRules'      : Lens RoundManagerEC SafetyRules
  rmSafetyRules'      = rmSafetyRules
  rmSyncOnly'         : Lens RoundManagerEC Bool
  rmSyncOnly'         = rmSyncOnly



  -- As seen below, this is sufficient to prove an RMLens instance for any lens that cannot change
  -- the EpochConfig (captured by the SameEpochCond data type along with properties
  -- RoundManagerEC-correct-≡ and α-EC-≡) and cannot change the BlockStore.  This suffices for all
  -- fields to RoundManagerEC except rmEpochState (potentially changes EpochConfig) and
  -- rmBlockstore.  For those we will need more targetted properties.
  rmLens-easy : ∀ {A} → (l : Lens RoundManagerEC A)
              → (∀ f rm1 → SameEpochCond rm1 (over l f rm1))
              → (∀ f rmec1 → (_rmBlockStore rmec1) ≡L (_rmBlockStore (over l f rmec1)) at (bsInner ∙ btIdToQuorumCert))
              → RMLens l
  rmLens-easy {A} l noEpochChange noBlockStoreChange =
    record { getRM = λ rm f →
               let rmec1 = _rmEC rm
                   rmec2 = over l f rmec1
                   sec   = noEpochChange f rmec1
                   𝓔s≡   = α-EC-≡ rmec1 rmec2 sec (_rmEC-correct rm)
                   bs≡   = noBlockStoreChange f rmec1
                   rmec2corr = RoundManagerEC-correct-≡ rmec1 rmec2 sec (_rmEC-correct rm)
               in (RoundManager∙new rmec2
                     rmec2corr
                     (RoundManagerWithMetaEC-subst1 rmec1 rmec2 (_rmEC-correct rm)
                                                    rmec2corr (_rmMetaWithEC rm) 𝓔s≡ bs≡))
                   , refl }

  instance
    rmLens-RoundState : RMLens rmRoundState'
    rmLens-RoundState = rmLens-easy rmRoundState' (λ _ rm → firstOne refl refl) (λ _ rm → refl)

    rmLens-SafetyRules : RMLens rmSafetyRules'
    rmLens-SafetyRules = rmLens-easy rmSafetyRules' (λ _ rm → firstOne refl refl) (λ _ rm → refl)

    rmLens-ProposerElection : RMLens rmProposerElection'
    rmLens-ProposerElection = rmLens-easy rmProposerElection' (λ _ rm → firstOne refl refl) (λ _ rm → refl)

    rmLens-SyncOnly : RMLens rmSyncOnly'
    rmLens-SyncOnly = rmLens-easy rmSyncOnly'     (λ _ rm → firstOne refl refl) (λ _ rm → refl)

    rmLens-BlockStore : RMLens rmBlockStore'
    rmLens-BlockStore = rmLens-easy rmBlockStore' (λ _ rm → firstOne refl refl) (λ _ rm → {!!})

    rmLens-EpochState : RMLens rmEpochState'
    rmLens-EpochState = rmLens-easy rmEpochState' {!!} (λ _ rm → refl)

  RM-∙-func : ∀ {A B} (l : Lens RoundManagerEC A)
             → ⦃ gl : RMLens l ⦄
             → (l' : Lens A B)
             → Lens RoundManagerEC B
  RM-∙-func l l' = l ∙ l'

  syntax RM-∙-func l l' = l RM-∙ l'

  RMLens-∙ : ∀ {A B} (l : Lens RoundManagerEC A)
             → ⦃ gl : RMLens l ⦄
             → (l' : Lens A B)
             → RMLens (l RM-∙ l')
  RMLens-∙ {A} {B} l ⦃ gl ⦄ l' =
    record { getRM = λ rm f → help rm f }
    where
      help : (rm : RoundManager) → (f : B → B)
           → Σ RoundManager (λ rm' → (rm' rmEC) ≡ over (l ∙ l') f (_rmEC rm))
      help rm f
         with getRM gl rm (_& l' %~ f)
      ... | rm' , prf = rm' , trans prf (over-∙ l l' f (_rmEC rm))

  rsPendingVotes' : Lens RoundState PendingVotes
  rsPendingVotes' = rsPendingVotes

  rsVoteSent' : Lens RoundState (Maybe Vote)
  rsVoteSent' = rsVoteSent

  lPendingVotes : Lens RoundManagerEC PendingVotes
  lPendingVotes = rmRoundState ∙ rsPendingVotes

  lBlockStore : Lens RoundManagerEC BlockStore
  lBlockStore = rmBlockStore

  lSafetyRules : Lens RoundManagerEC SafetyRules
  lSafetyRules = rmSafetyRules

  lRoundState : Lens RoundManagerEC RoundState
  lRoundState = rmRoundState

  lPersistentSafetyStorage : Lens RoundManagerEC PersistentSafetyStorage
  lPersistentSafetyStorage = rmSafetyRules ∙ srPersistentStorage

  lSafetyData : Lens RoundManagerEC SafetyData
  lSafetyData = lPersistentSafetyStorage ∙ pssSafetyData

  pvAuthorToVote' : Lens PendingVotes (KVMap Author Vote)
  pvAuthorToVote' = pvAuthorToVote

  pvMaybePartialTC' : Lens PendingVotes (Maybe TimeoutCertificate)
  pvMaybePartialTC' = pvMaybePartialTC

  pvLiDigestToVotes' : Lens PendingVotes (KVMap HashValue LedgerInfoWithSignatures)
  pvLiDigestToVotes' = pvLiDigestToVotes

  pvAuthorToVote-makeClassy : Lens RoundManagerEC (KVMap Author Vote)
  pvAuthorToVote-makeClassy = lPendingVotes ∙ pvAuthorToVote

  pvLiDigestToVotes-makeClassy : Lens RoundManagerEC (KVMap HashValue LedgerInfoWithSignatures)
  pvLiDigestToVotes-makeClassy = lPendingVotes ∙ pvLiDigestToVotes

  pvMaybePartialTC-makeClassy : Lens RoundManagerEC (Maybe TimeoutCertificate)
  pvMaybePartialTC-makeClassy = lPendingVotes ∙ pvMaybePartialTC

  rsVoteSent-makeClassy : Lens RoundManagerEC (Maybe Vote)
  rsVoteSent-makeClassy = lRoundState ∙ rsVoteSent

  lProposerElection : Lens RoundManagerEC ProposerElection
  lProposerElection = rmProposerElection'

  lSyncOnly : Lens RoundManagerEC Bool
  lSyncOnly = rmSyncOnly'

  rmLastVotedRound : Lens RoundManagerEC Round
  rmLastVotedRound = rmSafetyRules ∙ srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound

  instance
    rmLens-lPendingVotes : RMLens lPendingVotes
    rmLens-lPendingVotes = RMLens-∙ rmRoundState' rsPendingVotes'

    rmLens-1 : RMLens pvAuthorToVote-makeClassy
    rmLens-1 = RMLens-∙ lPendingVotes pvAuthorToVote'

    rmLens-2 : RMLens pvLiDigestToVotes-makeClassy
    rmLens-2 = RMLens-∙ lPendingVotes pvLiDigestToVotes'

    rmLens-3 : RMLens pvMaybePartialTC-makeClassy
    rmLens-3 = RMLens-∙ lPendingVotes pvMaybePartialTC'

    rmLens-4 : RMLens rmLastVotedRound
    rmLens-4 = RMLens-∙ rmSafetyRules' (srPersistentStorage ∙ pssSafetyData ∙ sdLastVotedRound)

    rmLens-5 : RMLens lSafetyData
    rmLens-5 = RMLens-∙ rmSafetyRules' (srPersistentStorage ∙ pssSafetyData)

    rmLens-6 : RMLens rsVoteSent-makeClassy
    rmLens-6 = RMLens-∙ rmRoundState' rsVoteSent'

{- Hopefully these will become obsolete

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

  module _ (rm : RoundManager) (bs : BlockStore) where
     rmEC' = record (_rmEC rm) { _rmBlockStore = bs }
     rmEC-correct' = RoundManagerEC-correct-≡ (_rmEC rm) rmEC' (firstOne refl refl) (_rmEC-correct rm)

     rmSetBlockStore : hasValidQCs (α-EC (rmEC' , rmEC-correct')) bs → RoundManager
     rmSetBlockStore hasvqc =
          record { _rmEC = rmEC'
                 ; _rmEC-correct = rmEC-correct'
                 ; _rmMetaWithEC = RoundManagerWithEC∙new  hasvqc }


{- Hopefully these will become obsolete

  rmGetBlockStore : (rm : RoundManager) → BlockStore (α-EC-RM rm)
  rmGetBlockStore rm = (_rmWithEC rm) ^∙ (epBlockStore (α-EC-RM rm))

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

-}

  -- This one will require more work.  We will need a proof that the setter doesn't change the
  -- fields that α-EC uses, or that α-EC still produces the same 𝓔, or that there is a new epoch
  -- config and dependent metadata.  In at least the latter case, this will be
  -- application-dependent.  E.g., if we change epochs, then we still change to valid parameters (so
  -- an EpochConfig can be produced) *and* that the BlockStore has validQCs (in practice, this will
  -- be because it has none because it's a new epoch, but again this is application dependent, so
  -- will have to come with a proof)
  rmGetValidatorVerifier : RoundManager → ValidatorVerifier
  rmGetValidatorVerifier rm = _esVerifier (_rmEpochState (_rmEC rm))

  -- IMPL-DIFF : this is defined as a lens getter only (no setter) in Haskell.
  rmPgAuthor : RoundManagerEC → Maybe Author
  rmPgAuthor rm =
    maybeS (rm ^∙ rmSafetyRules ∙ srValidatorSigner) nothing (just ∘ (_^∙ vsAuthor))

{- Hopefully these will become obsolete

  lSyncOnly : Lens RoundManager Bool
  lSyncOnly = mkLens' g s
    where
    g : RoundManager → Bool
    g rm = _rmEC rm ^∙ rmSyncOnly

    s : RoundManager → Bool → RoundManager
    s rm so = record rm { _rmEC = (_rmEC rm) & rmSyncOnly ∙~ so }

  lPersistentSafetyStorage : Lens RoundManager PersistentSafetyStorage
  lPersistentSafetyStorage = lSafetyRules ∙ srPersistentStorage

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

