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
open import LibraBFT.Impl.Handle
open import LibraBFT.Lemmas
open import LibraBFT.Prelude
open import Optics.All

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open        ParamsWithInitAndHandlers InitAndHandlers
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers PeerCanSignForPK PeerCanSignForPK-stable

module LibraBFT.Impl.Properties.Util where

module Meta where
  getLastVoteEpoch : RoundManager → Epoch
  getLastVoteEpoch rm = maybe{B = const Epoch} (_^∙ vEpoch) (rm ^∙ pssSafetyData-rm ∙ sdEpoch) ∘ (_^∙ pssSafetyData-rm ∙ sdLastVote) $ rm

  getLastVoteRound : RoundManager → Round
  getLastVoteRound = maybe{B = const Round} (_^∙ vRound) 0 ∘ (_^∙ pssSafetyData-rm ∙ sdLastVote)

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

module QCProps where

  record MsgRequirements (pool : SentMessages) (msg : NetworkMsg) : Set where
    constructor mkMsgRequirements
    field
      mSndr  : NodeId
      m∈pool : (mSndr , msg) ∈ pool

  record SyncInfoRequirements (pool : SentMessages) (syncInfo : SyncInfo) : Set where
    constructor mkSyncInfoRequirements
    field
      msg     : NetworkMsg
      msgReqs : MsgRequirements pool msg
      syncInfo∈msg : syncInfo SyncInfo∈NM msg
    open MsgRequirements msgReqs

  record BlockRequirements (pool : SentMessages) (block : Block) : Set where
    constructor mkBlockRequirements
    field
      msg       : NetworkMsg
      msgReqs   : MsgRequirements pool msg
      block∈msg : block Block∈Msg msg

  QCRequirements : (pool : SentMessages) (qc : QuorumCert) → Set
  QCRequirements pool qc =
    ∃[ si ] (qc QC∈SyncInfo si × SyncInfoRequirements pool si)
    ⊎ ⊥ -- TODO: qc came from aggregated votes received by proposer

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

  ∈Post⇒∈PreOr'-∙-BT-RM : _
  ∈Post⇒∈PreOr'-∙-BT-RM = ∈Post⇒∈PreOr'-∙ lBlockTree _∈BlockTree_ _∈RoundManager_ id id

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

  ∈Post⇒∈PreOr'-subst : ∀ {A : Set}
                      → (_QC∈_ : QuorumCert → A → Set)
                      → (_≡Prop_ : A → A → Set)
                      → (prf : (∀ {a1 a2 : A} → a1 ≡Prop a2 → (∀ {q} → (q QC∈ a2) → (q QC∈ a1))))
                      → ∀ {pre post}
                      → (Q : QuorumCert → Set)
                      → pre ≡Prop post
                      → ∈Post⇒∈PreOr' _QC∈_ Q pre post
  ∈Post⇒∈PreOr'-subst _ ≡Prop prf _ ≡P q = inj₁ ∘ prf ≡P

  ∈Post⇒∈PreOrBT-subst = ∈Post⇒∈PreOr'-subst _∈BlockTree_ _≡_ λ where refl → id

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
    → ¬(∈GenInfo-impl genesisInfo sig)
    → MsgWithSig∈ pk sig pool

  SigsForVotes∈Rm-SentB4 : SentMessages → RoundManager → Set
  SigsForVotes∈Rm-SentB4 pool rm = ∀ {qc v pk} → SigForVote∈Rm-SentB4 v pk qc rm pool

  ++-SigsForVote∈Rm-SentB4
    : ∀ {pool rm} → (msgs : SentMessages) → SigsForVotes∈Rm-SentB4 pool rm
      → SigsForVotes∈Rm-SentB4 (msgs ++ pool) rm
  ++-SigsForVote∈Rm-SentB4{pool} msgs sfvb4 qc∈rm sig vs∈qc rbld≈v ¬gen =
    MsgWithSig∈-++ʳ{ms = msgs} (sfvb4 qc∈rm sig vs∈qc rbld≈v ¬gen)

module RoundManagerInvariants where
  -- The property that a block tree `bt` has only valid QCs with respect to epoch config `𝓔`
  AllValidQCs : (𝓔 : EpochConfig) (bt : BlockTree) → Set
  AllValidQCs 𝓔 bt = (hash : HashValue) → maybe (WithEC.MetaIsValidQC 𝓔) ⊤ (lookup hash (bt ^∙ btIdToQuorumCert))

  module _ (rm : RoundManager) where
    EpochsMatch : Set
    EpochsMatch = rm ^∙ rmEpochState ∙ esEpoch ≡ rm ^∙ pssSafetyData-rm ∙ sdEpoch

    record BlockStoreInv : Set where
      constructor mkBlockTreeInv
      field
        allValidQCs : (rmC : RoundManager-correct rm) → AllValidQCs (α-EC-RM rm rmC) (rm ^∙ rmBlockStore ∙ bsInner)

    -- SafetyRules invariants
    record SafetyDataInv : Set where
      constructor mkSafetyDataInv
      field
        lvEpoch≡ : Meta.getLastVoteEpoch rm ≡ rm ^∙ pssSafetyData-rm ∙ sdEpoch
        lvRound≤ : Meta.getLastVoteRound rm ≤ rm ^∙ pssSafetyData-rm ∙ sdLastVotedRound

    record SafetyRulesInv : Set where
      constructor mkSafetyRulesInv
      field
        sdInv : SafetyDataInv

  -- NOTE: This will be proved by induction on reachable states using the
  -- property that peer handlers preserve invariants. That is to say, many of
  -- these cannot be proven as a post-condition of the peer handler: one can
  -- only prove of the handler that if the invariant holds for the prestate,
  -- then it holds for the poststate.
  record RoundManagerInv (rm : RoundManager) : Set where
    constructor mkRoundManagerInv
    field
      rmCorrect    : RoundManager-correct rm
      epochsMatch  : EpochsMatch rm
      btInv        : BlockStoreInv rm
      srInv        : SafetyRulesInv rm

  Preserves : ∀ {ℓ} → (P : RoundManager → Set ℓ) (pre post : RoundManager) → Set ℓ
  Preserves Pred pre post = Pred pre → Pred post

  PreservesL : ∀ {ℓ} {A : Set}
               → (P : RoundManager → Set ℓ) (l : Lens RoundManager A)
               → (a₁ a₂ : A) → Set ℓ
  PreservesL Pred l a₁ a₂ = ∀ rm → Preserves Pred (rm & l ∙~ a₁) (rm & l ∙~ a₂)

  reflPreserves : ∀ {ℓ} (P : RoundManager → Set ℓ) → Reflexive (Preserves P)
  reflPreserves Pred = id

  reflPreservesRoundManagerInv : Reflexive (Preserves RoundManagerInv)
  reflPreservesRoundManagerInv = reflPreserves RoundManagerInv

  transPreserves : ∀ {ℓ} (P : RoundManager → Set ℓ) → Transitive (Preserves P)
  transPreserves Pred p₁ p₂ = p₂ ∘ p₁

  transPreservesL : ∀ {ℓ} {A : Set}
                  → (P : RoundManager → Set ℓ) (l : Lens RoundManager A)
                  → {a₁ a₂ a₃ : A}
                  → PreservesL P l a₁ a₂
                  → PreservesL P l a₂ a₃
                  → PreservesL P l a₁ a₃
  transPreservesL Pred l p₁ p₂ rm = transPreserves Pred (p₁ rm) (p₂ rm)

  transPreservesRoundManagerInv : Transitive (Preserves RoundManagerInv)
  transPreservesRoundManagerInv = transPreserves RoundManagerInv

  substBlockStoreInv-qcMap
    : ∀ {rm₁ rm₂}
      → rm₁ ≡L rm₂ at (lBlockTree ∙ btIdToQuorumCert)
      → rm₁ ≡L rm₂ at rmEpochState ∙ esVerifier
      → Preserves BlockStoreInv rm₁ rm₂
  substBlockStoreInv-qcMap rmbs≡ rmvv≡ (mkBlockTreeInv allValidQCs) =
    mkBlockTreeInv (help rmbs≡ rmvv≡ allValidQCs)
    where
    help
      : ∀ {rm₁ rm₂}
        → rm₁ ≡L rm₂ at (lBlockTree ∙ btIdToQuorumCert)
        → rm₁ ≡L rm₂ at rmEpochState ∙ esVerifier
        → ((rmC : RoundManager-correct rm₁) → AllValidQCs (α-EC-RM rm₁ rmC) (rm₁ ^∙ rmBlockStore ∙ bsInner))
        → ((rmC : RoundManager-correct rm₂) → AllValidQCs (α-EC-RM rm₂ rmC) (rm₂ ^∙ rmBlockStore ∙ bsInner))
    help refl refl avqs rmc = obm-dangerous-magic' "TODO: waiting on definition of α-EC"

  substBlockStoreInv
    : ∀ {rm₁ rm₂}
      → rm₁ ≡L rm₂ at lBlockStore
      → rm₁ ≡L rm₂ at rmEpochState ∙ esVerifier
      → Preserves BlockStoreInv rm₁ rm₂
  substBlockStoreInv rmbs≡ rmvv≡ bti =
    substBlockStoreInv-qcMap (cong (_^∙ bsInner ∙ btIdToQuorumCert) rmbs≡) rmvv≡ bti

  substSigsForVotes∈Rm-SentB4
    : ∀ {pool pre post} → pre ≡L post at rmBlockStore
      → Preserves (QCProps.SigsForVotes∈Rm-SentB4 pool) pre post
  substSigsForVotes∈Rm-SentB4{pool}{pre}{post} bs≡ qcsB4 {qc} (QCProps.inHQC qc≡) sig vs∈qc rbld≈v =
    qcsB4 (QCProps.inHQC qc≡') sig vs∈qc rbld≈v
    where
    qc≡' : qc ≡ pre ^∙ lBlockStore ∙ bsInner ∙ btHighestQuorumCert
    qc≡' = trans qc≡ (cong (_^∙ bsInner ∙ btHighestQuorumCert) (sym bs≡))
  substSigsForVotes∈Rm-SentB4{pool}{pre}{post} bs≡ qcsB4 {qc} (QCProps.inHCC qc≡) sig vs∈qc rbld≈v =
    qcsB4 (QCProps.inHCC qc≡') sig vs∈qc rbld≈v
    where
    qc≡' : qc ≡ pre ^∙ lBlockStore ∙ bsInner ∙ btHighestCommitCert
    qc≡' = trans qc≡ (cong (_^∙ bsInner ∙ btHighestCommitCert) (sym bs≡))

  substSafetyDataInv
    : ∀ {pre post} → pre ≡L post at pssSafetyData-rm → Preserves SafetyDataInv pre post
  substSafetyDataInv{pre}{post} sd≡ (mkSafetyDataInv epoch≡ round≤) = mkSafetyDataInv epoch≡' round≤'
    where
    epoch≡' : Meta.getLastVoteEpoch post ≡ post ^∙ pssSafetyData-rm ∙ sdEpoch
    epoch≡' rewrite sym sd≡ = epoch≡

    round≤' : Meta.getLastVoteRound post ≤ post ^∙ pssSafetyData-rm ∙ sdLastVotedRound
    round≤' rewrite sym sd≡ = round≤

  mkPreservesSafetyRulesInv
    : ∀ {pre post}
      → Preserves SafetyDataInv pre post
      → Preserves SafetyRulesInv pre post
  mkPreservesSafetyRulesInv lvP (mkSafetyRulesInv lv) = mkSafetyRulesInv (lvP lv)

  mkPreservesRoundManagerInv
    : ∀ {pre post}
      → Preserves RoundManager-correct pre post
      → Preserves EpochsMatch          pre post
      → Preserves BlockStoreInv        pre post
      → Preserves SafetyRulesInv       pre post
      → Preserves RoundManagerInv      pre post
  mkPreservesRoundManagerInv rmP emP bsP srP (mkRoundManagerInv rmCorrect epochsMatch btInv srInv) =
    mkRoundManagerInv (rmP rmCorrect) (emP epochsMatch) (bsP btInv) (srP srInv)

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
