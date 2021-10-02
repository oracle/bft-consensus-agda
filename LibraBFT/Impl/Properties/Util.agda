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
import      LibraBFT.Impl.Handle as Handle
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.ImplShared.Util.HashCollisions Handle.RealHandler.InitAndHandlers
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open        ParamsWithInitAndHandlers Handle.RealHandler.InitAndHandlers
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms Handle.RealHandler.InitAndHandlers PeerCanSignForPK PeerCanSignForPK-stable

module LibraBFT.Impl.Properties.Util where

module Meta where
  getLastVoteEpoch : SafetyData → Epoch
  getLastVoteEpoch sd = (maybe{B = const Epoch} (_^∙ vEpoch) (sd ^∙ sdEpoch)) ∘ (_^∙ sdLastVote) $ sd
  -- getLastVoteEpoch rm = (maybe{B = const Epoch} (_^∙ vEpoch) (rm ^∙ pssSafetyData-rm ∙ sdEpoch)) ∘ (_^∙ pssSafetyData-rm ∙ sdLastVote) $ rm

  getLastVoteRound : SafetyData → Round
  getLastVoteRound = (maybe{B = const Round} (_^∙ vRound) 0) ∘ (_^∙ sdLastVote)
  -- getLastVoteRound = maybe{B = const Round} (_^∙ vRound) 0 ∘ (_^∙ pssSafetyData-rm ∙ sdLastVote)

  subst-getLastVoteRound : ∀ {sd1 sd2} → sd1 ≡ sd2 → getLastVoteRound sd1 ≡ getLastVoteRound sd2
  subst-getLastVoteRound refl = refl

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
      filter-∪?-[]₁ outs isBroadcastProposal? _ noMsgs
    proj₁ (proj₂ (NoMsgs⇒× noMsgs)) =
      filter-∪?-[]₂ outs _ isSendVote?
        (filter-∪?-[]₂ outs _ _ noMsgs)
    proj₂ (proj₂ (NoMsgs⇒× noMsgs)) =
      filter-∪?-[]₁ outs isBroadcastSyncInfo? _
        (filter-∪?-[]₂ outs _ _ noMsgs)

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


module BlockProps (b : Block) where
  ∈BlockTree_      : BlockTree → Set
  ∈BlockTree bt    = ∃[ eb ] (btGetBlock (b ^∙ bId) bt ≡ just eb)

  ∈BlockStore_     : BlockStore → Set
  ∈BlockStore bs   = ∈BlockTree (bs ^∙ bsInner)

  ∈RoundManager_   : RoundManager → Set
  ∈RoundManager rm = ∈BlockStore (rm ^∙ lBlockStore)

module QCProps where

  data _∈BlockTree_ (qc : QuorumCert) (bt : BlockTree) : Set where
    inHQC : qc ≡ bt ^∙ btHighestQuorumCert → qc ∈BlockTree bt
    inHCC : qc ≡ bt ^∙ btHighestCommitCert → qc ∈BlockTree bt

  _∈RoundManager_ : (qc : QuorumCert) (rm : RoundManager) → Set
  qc ∈RoundManager rm =  qc ∈BlockTree (rm ^∙ lBlockStore ∙ bsInner)


  ∈Post⇒∈PreOr' : ∀ {A : Set} (_QC∈_ : QuorumCert → A → Set) (Q : QuorumCert → Set) (pre post : A) → Set
  ∈Post⇒∈PreOr' _QC∈_ Q pre post = ∀ qc → qc QC∈ post → qc QC∈ pre ⊎ Q qc

  ∈Post⇒∈PreOr'-∙ : ∀ {A B : Set}
                    → (l : Lens A B)
                    → (_QC∈B_ : QuorumCert → B → Set)
                    → (_QC∈A_ : QuorumCert → A → Set)
                    → (∀ {q st} → q QC∈B (st ^∙ l) → q QC∈A st)
                    → (∀ {q st} → q QC∈A st → q QC∈B (st ^∙ l))
                    → (Q : QuorumCert → Set)
                    → (pre post : A)
                    → ∈Post⇒∈PreOr' _QC∈B_ Q (pre ^∙ l) (post ^∙ l)
                    → ∈Post⇒∈PreOr' _QC∈A_ Q pre post
  ∈Post⇒∈PreOr'-∙ l _QC∈B_ _QC∈A_ prfBA prfAB Q pre post QCB qc qc∈Apost =
    ⊎-map₁ prfBA (QCB qc (prfAB qc∈Apost))

  ∈Post⇒∈PreOr-∙-BT-RM : _
  ∈Post⇒∈PreOr-∙-BT-RM = ∈Post⇒∈PreOr'-∙ lBlockTree _∈BlockTree_ _∈RoundManager_ id id

  ∈Post⇒∈PreOrBT : (Q : QuorumCert → Set) (pre post : BlockTree) → Set
  ∈Post⇒∈PreOrBT = ∈Post⇒∈PreOr' _∈BlockTree_

  ∈BlockTree-upd-hqc : ∀ {bt1 bt2}
                       → {Q : QuorumCert → Set}
                       → bt1 ≡L bt2 at btHighestCommitCert
                       → Q (bt2 ^∙ btHighestQuorumCert)
                       → ∈Post⇒∈PreOrBT Q bt1 bt2
  ∈BlockTree-upd-hqc refl Q _ (inHQC refl) = inj₂ Q
  ∈BlockTree-upd-hqc refl _ _ (inHCC refl) = inj₁ (inHCC refl)

  ∈BlockTree-upd-hcc : ∀ {bt1 bt2}
                       → {Q : QuorumCert → Set}
                       → bt1 ≡L bt2 at btHighestQuorumCert
                       → Q (bt2 ^∙ btHighestCommitCert)
                       → ∈Post⇒∈PreOrBT Q bt1 bt2
  ∈BlockTree-upd-hcc refl _ _ (inHQC refl) = inj₁ (inHQC refl)
  ∈BlockTree-upd-hcc refl Q _ (inHCC refl) = inj₂ Q

  ∈Post⇒∈PreOr : (Q : QuorumCert → Set) (pre post : RoundManager) → Set
  ∈Post⇒∈PreOr = ∈Post⇒∈PreOr' _∈RoundManager_

  ∈Post⇒∈PreOr'-refl : ∀ {A : Set}
                      → (_QC∈_ : QuorumCert → A → Set) (Q : QuorumCert → Set)
                      → ∀ {pre : A}
                      → ∈Post⇒∈PreOr' _QC∈_ Q pre pre
  ∈Post⇒∈PreOr'-refl _ _ _ = inj₁

  ∈Post⇒∈PreOrBT-QCs≡ : ∀ {bt1 bt2}
                        → (Q : QuorumCert → Set)
                        → bt1 ≡L bt2 at btHighestCommitCert
                        → bt1 ≡L bt2 at btHighestQuorumCert
                        → ∈Post⇒∈PreOrBT Q bt1 bt2
  ∈Post⇒∈PreOrBT-QCs≡ Q refl refl _ (inHQC refl) = inj₁ (inHQC refl)
  ∈Post⇒∈PreOrBT-QCs≡ Q refl refl _ (inHCC refl) = inj₁ (inHCC refl)

  ∈Post⇒∈PreOr'-trans : ∀ {A : Set}
                      → (_QC∈_ : QuorumCert → A → Set) (Q : QuorumCert → Set)
                      → ∀ {pre int post : A}
                      → ∈Post⇒∈PreOr' _QC∈_ Q pre int
                      → ∈Post⇒∈PreOr' _QC∈_ Q int post
                      → ∈Post⇒∈PreOr' _QC∈_ Q pre post
  ∈Post⇒∈PreOr'-trans _QC∈_ Q pre→int int→post qc qc∈post
     with int→post qc qc∈post
  ... | Right y = Right y
  ... | Left  x
     with pre→int qc x
  ... | Right y = Right y
  ... | Left x₁ = Left x₁

  ∈Post⇒∈PreOrBT-trans : ∀ (Q : QuorumCert → Set) {pre int post}
                       → ∈Post⇒∈PreOrBT Q pre int
                       → ∈Post⇒∈PreOrBT Q int post
                       → ∈Post⇒∈PreOrBT Q pre post
  ∈Post⇒∈PreOrBT-trans = ∈Post⇒∈PreOr'-trans _∈BlockTree_

  -- TODO-1: Factor out a property about a single output:
  -- λ out → ∃₂ λ qc nm → qc QC∈NM nm × nm Msg∈Out out
  OutputQc∈RoundManager : List Output → RoundManager → Set
  OutputQc∈RoundManager outs rm =
    All (λ out → ∀ qc nm → qc QC∈NM nm → nm Msg∈Out out → qc ∈RoundManager rm) outs

  ¬OutputQc : List Output → Set
  ¬OutputQc outs = All (λ out → ∀ qc nm → qc QC∈NM nm → nm Msg∈Out out → ⊥) outs

  ++-OutputQc∈RoundManager
    : ∀ {rm outs₁ outs₂}
      → OutputQc∈RoundManager outs₁ rm → OutputQc∈RoundManager outs₂ rm
      → OutputQc∈RoundManager (outs₁ ++ outs₂) rm
  ++-OutputQc∈RoundManager = All-++

  ++-¬OutputQc : ∀ {outs₁ outs₂} → ¬OutputQc outs₁ → ¬OutputQc outs₂
                 → ¬OutputQc (outs₁ ++ outs₂)
  ++-¬OutputQc = All-++

  NoMsgs⇒¬OutputQc : ∀ outs → OutputProps.NoMsgs outs → ¬OutputQc outs
  NoMsgs⇒¬OutputQc outs noMsgs =
    All-map help (noneOfKind⇒All¬ outs _ noMsgs)
    where
    help : ∀ {out : Output} → ¬ IsOutputMsg out → ∀ qc nm → qc QC∈NM nm → nm Msg∈Out out → ⊥
    help ¬msg qc .(P _) qc∈m inBP = ¬msg (Left tt)
    help ¬msg qc .(V _) qc∈m inSV = ¬msg (Right (Right tt))

  ¬OutputQc⇒OutputQc∈RoundManager : ∀ outs rm → ¬OutputQc outs → OutputQc∈RoundManager outs rm
  ¬OutputQc⇒OutputQc∈RoundManager outs rm noOutQcs =
    All-map (λ ¬outqc qc nm qc∈nm nm∈out → ⊥-elim (¬outqc qc nm qc∈nm nm∈out))
      noOutQcs

  NoMsgs⇒OutputQc∈RoundManager : ∀ outs rm → OutputProps.NoMsgs outs → OutputQc∈RoundManager outs rm
  NoMsgs⇒OutputQc∈RoundManager outs rm noMsgs =
    ¬OutputQc⇒OutputQc∈RoundManager outs rm (NoMsgs⇒¬OutputQc outs noMsgs)

  SigForVote∈Rm-SentB4 : Vote → PK → QuorumCert → RoundManager → SentMessages → Set
  SigForVote∈Rm-SentB4 v pk qc rm pool =
    qc ∈RoundManager rm
    → WithVerSig pk v →
    ∀ {vs : Author × Signature} → let (pid , sig) = vs in
      vs ∈ qcVotes qc → rebuildVote qc vs ≈Vote v
    → ¬(∈BootstrapInfo-impl fakeBootstrapInfo sig)
    → MsgWithSig∈ pk sig pool

  SigsForVotes∈Rm-SentB4 : SentMessages → RoundManager → Set
  SigsForVotes∈Rm-SentB4 pool rm = ∀ {qc v pk} → SigForVote∈Rm-SentB4 v pk qc rm pool

  ++-SigsForVote∈Rm-SentB4
    : ∀ {pool rm} → (msgs : SentMessages) → SigsForVotes∈Rm-SentB4 pool rm
      → SigsForVotes∈Rm-SentB4 (msgs ++ pool) rm
  ++-SigsForVote∈Rm-SentB4{pool} msgs sfvb4 qc∈rm sig vs∈qc rbld≈v ¬bootstrap =
    MsgWithSig∈-++ʳ{ms = msgs} (sfvb4 qc∈rm sig vs∈qc rbld≈v ¬bootstrap)

module Invariants where

  ------------ properties relating the ids of (Executed)Blocks to hashes of their BlockData

  BlockHash≡ : Block → HashValue → Set
  BlockHash≡ b hv =  hashBlock b ≡ hv

  BlockId-correct : Block → Set
  BlockId-correct b = BlockHash≡ b (b ^∙ bId)

  BlockId-correct? : (b : Block) → Dec (BlockId-correct b)
  BlockId-correct? b = hashBlock b ≟Hash (b ^∙ bId)

  ExecutedBlockId-correct : ExecutedBlock → Set
  ExecutedBlockId-correct = BlockId-correct ∘ (_^∙ ebBlock)

  ------------ properties for BlockTree validity

  -- The property that a block tree `bt` has only valid QCs with respect to epoch config `𝓔`
  AllValidQCs : (𝓔 : EpochConfig) (bt : BlockTree) → Set
  AllValidQCs 𝓔 bt = (hash : HashValue) → maybe (WithEC.MetaIsValidQC 𝓔) ⊤ (lookup hash (bt ^∙ btIdToQuorumCert))

  -- TODO: define a record?
  ValidEValidBlock         = Σ Block         BlockId-correct

  AllValidBlocks : BlockTree → Set
  AllValidBlocks bt = ∀ {bid eb}
                    → btGetBlock bid bt ≡ just eb
                    → BlockId-correct (eb ^∙ ebBlock) × BlockHash≡ (eb ^∙ ebBlock)  bid

  ------------ types for and definitions of invariants for BlockTree, BlockStore, SafetyData, SafetyRules

  record ECinfo : Set where
    constructor mkECinfo
    field
      ecVV : ValidatorVerifier
      ecEP : Epoch
  open ECinfo

  WithECinfo : Set → Set
  WithECinfo A = A × ECinfo

  BlockTree-EC  = WithECinfo BlockTree
  BlockStore-EC = WithECinfo BlockStore

  module _ (btEC : BlockTree-EC) where
    private
      bt  = proj₁ btEC
      eci = proj₂ btEC
      vv = ecVV eci
      ep = ecEP eci

    record BlockTreeInv : Set where
      constructor mkBlockTreeInv
      field
        allValidQCs    : (vvC : ValidatorVerifier-correct $ vv) → AllValidQCs (α-EC-VV (vv , vvC) ep) bt
        allValidBlocks : AllValidBlocks bt
  open BlockTreeInv

  module _ (bsEC : BlockStore-EC) where
    private
      bs   = proj₁ bsEC
      eci =  proj₂ bsEC

    record BlockStoreInv : Set where
      constructor mkBlockStoreInv
      field
        blockTreeValid : BlockTreeInv (bs ^∙ bsInner , eci)
  open BlockStoreInv

  module _ (sd : SafetyData) where
    -- SafetyRules invariants
    record SafetyDataInv : Set where
      constructor mkSafetyDataInv
      field
        lvEpoch≡ : Meta.getLastVoteEpoch sd ≡ sd ^∙ sdEpoch
        lvRound≤ : Meta.getLastVoteRound sd ≤ sd ^∙ sdLastVotedRound

  module _ (sr : SafetyRules) where
    -- SafetyRules invariants
    record SafetyRulesInv : Set where
      constructor mkSafetyRulesInv
      field
        sdInv : SafetyDataInv (sr ^∙ srPersistentStorage ∙ pssSafetyData)
  open SafetyRulesInv

  ------------ types for and definition of RoundManagerInv

  EpochsMatch : RoundManager → Set
  EpochsMatch rm = rm ^∙ rmEpochState ∙ esEpoch ≡ rm ^∙ pssSafetyData-rm ∙ sdEpoch

  rm→ECinfo : RoundManager → ECinfo
  rm→ECinfo rm = mkECinfo (rm ^∙ rmEpochState ∙ esVerifier) (rm ^∙ rmEpoch)

  rm→BlockTree-EC : RoundManager → BlockTree-EC
  rm→BlockTree-EC rm = (rm ^∙ lBlockStore ∙ bsInner , rm→ECinfo rm)

  rm→BlockStore-EC : RoundManager → BlockStore-EC
  rm→BlockStore-EC rm = (rm ^∙ lBlockStore , rm→ECinfo rm)

  -- NOTE: This will be proved by induction on reachable states using the
  -- property that peer handlers preserve invariants. That is to say, many of
  -- these cannot be proven as a post-condition of the peer handler: one can
  -- only prove of the handler that if the invariant holds for the prestate,
  -- then it holds for the poststate.

  record RoundManagerInv (rm : RoundManager) : Set where
    constructor mkRoundManagerInv
    field
      rmCorrect        : ValidatorVerifier-correct (rm ^∙ rmValidatorVerifer)
      rmEpochsMatch    : EpochsMatch rm
      rmBlockStoreInv  : BlockStoreInv  (rm→BlockStore-EC rm)
      rmSafetyRulesInv : SafetyRulesInv (rm ^∙ lSafetyRules)
  open RoundManagerInv

  hash≡⇒≈Block : ∀ {b1 b2 : Block}
               → BlockId-correct b1
               → BlockId-correct b2
               → BlockHash≡ b1 (b2 ^∙ bId)
               → b1 ≈Block b2
  hash≡⇒≈Block {b1} {b2} refl refl hashb1≡idb2
     with hashBD-inj hashb1≡idb2
  ...| bdInj = sameBlockData⇒≈ {b1} {b2} hashb1≡idb2 bdInj

  module Reqs (b : Block) (bt : BlockTree) where
    -- TODO: State and use assumptions about hash collisions.  The following is one example that will
    -- likely need to be refined.
    NoHC1 = ∀ {eb}
            → btGetBlock (b ^∙ bId) bt ≡ just eb
            → BlockId-correct b
            → (eb ^∙ ebBlock) ≈Block b

  -- TODO: probably don't need this generality, consider moving into Handle.Properties (only place
  -- it is used so far), then we could streamline as rmi is required only to avoid cyclic lookups
  module _ {st} (reach : ReachableSystemState st)
           {pm : ProposalMsg} {sndr : NodeId} (nm∈pool : (sndr , P pm) ∈ msgPool st)
           (pid : NodeId) (ini : initialised st pid ≡ initd) where

    open PerReachableState reach

    private
      rm  = peerStates st pid
      bt  = rm ^∙ lBlockTree
      b   = pm ^∙ pmProposal

    nohc : RoundManagerInv rm
         → rm ^∙ lBlockTree ≡ bt
         → BlockId-correct b
         → Reqs.NoHC1 b bt
    nohc rmi refl refl {eb} jeb refl
       with allValidBlocks (blockTreeValid (rmBlockStoreInv rmi)) jeb
    ...| bidCorr , bid
       with (blockData-bsl (b ^∙ bBlockData)) ≟-BSL (blockData-bsl (eb ^∙ ebBlock ∙ bBlockData))
    ...| yes bsls≡ = hash≡⇒≈Block {eb ^∙ ebBlock} {b} bidCorr refl bid
    ...| no  neq rewrite sym bid
       = ⊥-elim (meta-specific-cr (msgRmHC (inP nm∈pool (inPM inB))
                                            ini
                                            (inRM (inBS jeb inB))
                                            (sym bid)
                                            neq))

  -- Valid blocks have IDs computed by the hash of their BlockData
  -- These are passed as module parameters through the proofs

  ValidBlock = Σ Block BlockId-correct

  vbBlock : ValidBlock → Block
  vbBlock = proj₁

  vbValid : (vb : ValidBlock) → BlockId-correct (vbBlock vb)
  vbValid = proj₂

  ------------ Preserves and related definitions and utilities

  Preserves : ∀ {ℓ} {A : Set} → (P : A → Set ℓ) (pre post : A) → Set ℓ
  Preserves Pred pre post = Pred pre → Pred post

  PreservesL : ∀ {ℓ} {A B : Set}
               → (P : A → Set ℓ) (l : Lens A B)
               → (b₁ b₂ : B) → Set ℓ
  PreservesL Pred l b₁ b₂ = ∀ a → Preserves Pred (a & l ∙~ b₁) (a & l ∙~ b₂)

  reflPreserves : ∀ {ℓ} {A : Set} (P : A → Set ℓ) → Reflexive (Preserves P)
  reflPreserves Pred = id

  reflPreservesRoundManagerInv : Reflexive (Preserves RoundManagerInv)
  reflPreservesRoundManagerInv = reflPreserves RoundManagerInv

  transPreserves : ∀ {ℓ} {A : Set} (P : A → Set ℓ) → Transitive (Preserves P)
  transPreserves Pred p₁ p₂ = p₂ ∘ p₁

  transPreservesL : ∀ {ℓ} {A B : Set}
                  → (P : A → Set ℓ) (l : Lens A B)
                  → {b₁ b₂ b₃ : B}
                  → PreservesL P l b₁ b₂
                  → PreservesL P l b₂ b₃
                  → PreservesL P l b₁ b₃
  transPreservesL Pred l p₁ p₂ a = transPreserves Pred (p₁ a) (p₂ a)

  transPreservesRoundManagerInv : Transitive (Preserves RoundManagerInv)
  transPreservesRoundManagerInv = transPreserves RoundManagerInv

  BSInv⇒BTInv-pres : ∀ {eci} {pre post : BlockStore}
                   → Preserves BlockStoreInv (pre , eci) (post , eci)
                   → Preserves BlockTreeInv (pre ^∙ bsInner , eci) (post ^∙ bsInner , eci)
  BSInv⇒BTInv-pres presBS btiPre = BlockStoreInv.blockTreeValid (presBS $ mkBlockStoreInv btiPre)

  mkPreservesSafetyRulesInv
    : ∀ {pre post}
      → Preserves SafetyDataInv (pre ^∙ srPersistentStorage ∙ pssSafetyData) (post ^∙ srPersistentStorage ∙ pssSafetyData)
      → Preserves SafetyRulesInv pre post
  mkPreservesSafetyRulesInv lvP (mkSafetyRulesInv lv) = mkSafetyRulesInv (lvP lv)

  mkPreservesRoundManagerInv
    : ∀ {pre post}
      → Preserves ValidatorVerifier-correct (pre ^∙ rmValidatorVerifer) (post ^∙ rmValidatorVerifer)
      → Preserves EpochsMatch                pre                         post
      → Preserves BlockStoreInv             (rm→BlockStore-EC pre)      (rm→BlockStore-EC post)
      → Preserves SafetyRulesInv            (pre ^∙ rmSafetyRules)      (post ^∙ rmSafetyRules)
      → Preserves RoundManagerInv            pre                         post
  mkPreservesRoundManagerInv rmP emP bsP srP (mkRoundManagerInv rmCorrect epochsMatch bsInv srInv) =
    mkRoundManagerInv (rmP rmCorrect) (emP epochsMatch) (bsP bsInv) (srP srInv)

module RoundManagerTransProps where
  -- Relations between the pre/poststate which may or may not hold, depending on
  -- the particular peer handler invoked

  -- - The epoch is unchanged
  NoEpochChange : (pre post : RoundManager) → Set
  NoEpochChange pre post = pre ≡L post at rmEpoch

  reflNoEpochChange : Reflexive NoEpochChange
  reflNoEpochChange = refl

  transNoEpochChange : Transitive NoEpochChange
  transNoEpochChange = trans

  NoSafetyDataChange : (pre post : RoundManager) → Set
  NoSafetyDataChange pre post = pre ≡L post at pssSafetyData-rm

  reflNoSafetyDataChange : Reflexive NoSafetyDataChange
  reflNoSafetyDataChange = refl

  transNoSafetyDataChange : Transitive NoSafetyDataChange
  transNoSafetyDataChange = trans

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

  open Invariants

  VoteEpochIs : (vote : Vote) (e : Epoch) → Set
  VoteEpochIs vote e = vote ^∙ vEpoch ≡ e

  VoteRoundIs : (vote : Vote) (r : Round) → Set
  VoteRoundIs vote r = vote ^∙ vRound ≡ r

  record VoteMadeFromBlock (vote : Vote) (block : Block) : Set where
    constructor mkVoteMadeFromBlock
    field
      epoch≡      : vote ^∙ vEpoch ≡ block ^∙ bEpoch
      round≡      : vote ^∙ vRound ≡ block ^∙ bRound
      proposedId≡ : vote ^∙ vProposedId ≡ block ^∙ bId

  VoteMadeFromBlock⇒VoteEpochRoundIs : ∀ {v b} → VoteMadeFromBlock v b → VoteEpochIs v (b ^∙ bEpoch) × VoteRoundIs v (b ^∙ bRound)
  VoteMadeFromBlock⇒VoteEpochRoundIs (mkVoteMadeFromBlock epoch≡ round≡ proposedID) = epoch≡ , round≡

  VoteTriggeredByBlock : (vote : Vote) (block : Block) (new? : Bool) → Set
  VoteTriggeredByBlock vote block true = VoteMadeFromBlock vote block
  VoteTriggeredByBlock vote block false = VoteRoundIs vote (block ^∙ bRound)

  record VoteGeneratedCorrect (pre post : RoundManager) (vote : Vote) (block : Block) : Set where
    constructor mkVoteGeneratedCorrect
    field
      state          : RoundManagerTransProps.VoteGenerated pre post vote
    voteNew? = RoundManagerTransProps.isVoteNewGenerated pre post vote state
    field
      blockTriggered : VoteTriggeredByBlock vote block voteNew?

  substVoteGeneratedCorrect
    : ∀ {pre post vote} (block₁ block₂ : Block) → block₁ ≈Block block₂
      → VoteGeneratedCorrect pre post vote block₁ → VoteGeneratedCorrect pre post vote block₂
  substVoteGeneratedCorrect block₁ block₂ bd≡ (mkVoteGeneratedCorrect state blockTriggered)
     with state
  ...| RoundManagerTransProps.mkVoteGenerated lv≡v voteSrc
     with voteSrc
  ...| Left vog rewrite bd≡ =
     mkVoteGeneratedCorrect (RoundManagerTransProps.mkVoteGenerated lv≡v (Left vog)) blockTriggered
  ...| Right vng
     with blockTriggered
  ...| mkVoteMadeFromBlock epoch≡ round≡ proposedID rewrite bd≡
     = mkVoteGeneratedCorrect
         (RoundManagerTransProps.mkVoteGenerated lv≡v (Right vng))
         (mkVoteMadeFromBlock epoch≡ round≡ proposedID)

  record VoteGeneratedUnsavedCorrect (pre post : RoundManager) (block : Block) : Set where
    constructor mkVoteGeneratedUnsavedCorrect
    field
      vote           : Vote
      voteGenCorrect : VoteGeneratedCorrect pre post vote block

  glue-VoteGeneratedCorrect-VoteNotGenerated
    : ∀ {s₁ s₂ s₃ vote block}
      → VoteGeneratedCorrect s₁ s₂ vote block
      → RoundManagerTransProps.VoteNotGenerated s₂ s₃ true
      → VoteGeneratedCorrect s₁ s₃ vote block
  glue-VoteGeneratedCorrect-VoteNotGenerated vgc@(mkVoteGeneratedCorrect vg@(RoundManagerTransProps.mkVoteGenerated lv≡v (inj₁ oldVG)) blockTriggered) vng =
    mkVoteGeneratedCorrect (RoundManagerTransProps.glue-VoteGenerated-VoteNotGenerated vg vng) blockTriggered
  glue-VoteGeneratedCorrect-VoteNotGenerated vgc@(mkVoteGeneratedCorrect vg@(RoundManagerTransProps.mkVoteGenerated lv≡v (inj₂ newVG)) blockTriggered) vng =
    mkVoteGeneratedCorrect (RoundManagerTransProps.glue-VoteGenerated-VoteNotGenerated vg vng) blockTriggered

  glue-VoteNotGenerated-VoteGeneratedCorrect
    : ∀ {s₁ s₂ s₃ vote block}
      → RoundManagerTransProps.VoteNotGenerated s₁ s₂ true
      → VoteGeneratedCorrect s₂ s₃ vote block
      → VoteGeneratedCorrect s₁ s₃ vote block
  glue-VoteNotGenerated-VoteGeneratedCorrect vng (mkVoteGeneratedCorrect vg@(RoundManagerTransProps.mkVoteGenerated lv≡v (inj₁ oldVG)) blockTriggered) =
    mkVoteGeneratedCorrect (RoundManagerTransProps.glue-VoteNotGenerated-VoteGenerated vng vg) blockTriggered
  glue-VoteNotGenerated-VoteGeneratedCorrect vng (mkVoteGeneratedCorrect vg@(RoundManagerTransProps.mkVoteGenerated lv≡v (inj₂ newVG)) blockTriggered) =
    mkVoteGeneratedCorrect (RoundManagerTransProps.glue-VoteNotGenerated-VoteGenerated vng vg)
      blockTriggered

  glue-VoteNotGenerated-VoteGeneratedUnsavedCorrect
    : ∀ {s₁ s₂ s₃ block}
      → RoundManagerTransProps.VoteNotGenerated s₁ s₂ true
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
      nvg⊎vgusc    : RoundManagerTransProps.VoteNotGenerated pre post lvr≡? ⊎ VoteGeneratedUnsavedCorrect pre post block

  glue-VoteNotGenerated-VoteUnsentCorrect
    : ∀ {s₁ s₂ s₃ outs₁ outs₂ block lvr≡?}
      → RoundManagerTransProps.VoteNotGenerated s₁ s₂ true → OutputProps.NoVotes outs₁
      → VoteUnsentCorrect s₂ s₃ outs₂ block lvr≡?
      → VoteUnsentCorrect s₁ s₃ (outs₁ ++ outs₂) block lvr≡?
  glue-VoteNotGenerated-VoteUnsentCorrect{outs₁ = outs₁} vng₁ nvo (mkVoteUnsentCorrect noVoteMsgOuts (inj₁ vng₂)) =
    mkVoteUnsentCorrect (OutputProps.++-NoVotes outs₁ _ nvo noVoteMsgOuts) (inj₁ (RoundManagerTransProps.transVoteNotGenerated vng₁ vng₂))
  glue-VoteNotGenerated-VoteUnsentCorrect{outs₁ = outs₁} vng₁ nvo (mkVoteUnsentCorrect noVoteMsgOuts (inj₂ vgus)) =
    mkVoteUnsentCorrect ((OutputProps.++-NoVotes outs₁ _ nvo noVoteMsgOuts)) (inj₂ (glue-VoteNotGenerated-VoteGeneratedUnsavedCorrect vng₁ vgus))

  -- The handler correctly attempted to vote on `block`, assuming the safety
  -- data epoch matches the block epoch.
  VoteAttemptCorrect : (pre post : RoundManager) (outs : List Output) (block : Block) → Set
  VoteAttemptCorrect pre post outs block =
    (∃[ lvr≡? ] VoteUnsentCorrect pre post outs block lvr≡?) ⊎ VoteSentCorrect pre post outs block

  -- The voting process ended before `pssSafetyData-rm` could be updated
  voteAttemptBailed : ∀ {rm block} outs → OutputProps.NoVotes outs → VoteAttemptCorrect rm rm outs block
  voteAttemptBailed outs noVotesOuts = inj₁ (true , mkVoteUnsentCorrect noVotesOuts (inj₁ RoundManagerTransProps.reflVoteNotGenerated))

  glue-VoteNotGenerated-VoteAttemptCorrect
    : ∀ {s₁ s₂ s₃ outs₁ outs₂ block}
      → RoundManagerTransProps.VoteNotGenerated s₁ s₂ true → OutputProps.NoVotes outs₁
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
