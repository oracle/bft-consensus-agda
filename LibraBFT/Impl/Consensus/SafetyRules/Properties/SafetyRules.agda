{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Types.ValidatorSigner               as ValidatorSigner
open import LibraBFT.Impl.Consensus.Types
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
open import LibraBFT.Impl.Consensus.SafetyRules.SafetyRules
import      LibraBFT.Impl.Util.Crypto                         as Crypto
open import LibraBFT.Impl.Util.Util

module LibraBFT.Impl.Consensus.SafetyRules.Properties.SafetyRules where

open RWST-do

module VerifyAndUpdatePreferredRoundM (quorumCert : QuorumCert) (safetyData : SafetyData) where
  preferredRound = safetyData ^∙ sdPreferredRound
  oneChainRound  = quorumCert ^∙ qcCertifiedBlock ∙ biRound
  twoChainRound  = quorumCert ^∙ qcParentBlock ∙ biRound

  C₁ = ⌊ oneChainRound <? preferredRound ⌋ ≡_
  C₂ = ⌊ twoChainRound >? preferredRound ⌋ ≡_
  C₃ = ⌊ twoChainRound <? preferredRound ⌋ ≡_
  C₄ = ⌊ twoChainRound ≟  preferredRound ⌋ ≡_

  contract
    : ∀ P pre
      → (C₁ true → P (inj₁ unit) pre [])
      → (C₁ false
         → (C₂ true → P (inj₂ (safetyData [ sdPreferredRound := twoChainRound ])) pre [])
           × (C₃ true → P (inj₂ safetyData) pre [])
           × (C₄ true → P (inj₂ safetyData) pre []))
      → RWST-weakestPre (verifyAndUpdatePreferredRoundM quorumCert safetyData) P unit pre
  proj₁ (contract P₁ pre b o) = b
  proj₁ (proj₂ (contract P₁ pre b o) c₁f) c₂t = proj₁ (o c₁f) c₂t
  proj₁ (proj₂ (proj₂ (contract P₁ pre b o) c₁f) c₂f) c₃t = proj₁ (proj₂ (o c₁f)) c₃t
  proj₂ (proj₂ (proj₂ (contract P₁ pre b o) c₁f) c₂f) c₃f
    with twoChainRound ≟ preferredRound
  ...| yes proof = proj₂ (proj₂ (o c₁f)) refl
  ...| no  proof
     with twoChainRound >? preferredRound
     |    twoChainRound <? preferredRound
  ...| no pf₁ | no pf₂
     with <-cmp twoChainRound preferredRound
  ... | tri< imp _ _ = ⊥-elim (pf₂ imp)
  ... | tri≈ _ imp _ = ⊥-elim (proof imp)
  ... | tri> _ _ imp = ⊥-elim (pf₁ imp)

  contract-rwst
    : ∀ P pre
      → P (inj₁ unit) pre []
      → (∀ safetyData → P (inj₂ safetyData) pre [])
      → RWST-weakestPre (verifyAndUpdatePreferredRoundM quorumCert safetyData) P unit pre
  contract-rwst Post pre b o =
    contract Post pre (λ _ → b)
      (λ _ →   (λ _ → o ( safetyData [ sdPreferredRound := twoChainRound ]))
             , (λ _ → o safetyData)
             , λ _ → o safetyData)

  contract-rwst-∙?∙
    : ∀ {A} P pre (m : SafetyData → LBFT (ErrLog ⊎ A))
      → P (inj₁ unit) pre []
      → (∀ safetyData1 → RWST-weakestPre (m safetyData1) P unit pre)
      → RWST-weakestPre (verifyAndUpdatePreferredRoundM quorumCert safetyData ∙?∙ m) P unit pre
  proj₁ (contract-rwst-∙?∙ Post pre m b o) =
    contract-rwst (λ x post outs → (c : ErrLog) → x ≡ inj₁ c → Post (inj₁ c) post outs) pre
      (λ {unit _ → b})
      λ { _ _ ()}
  proj₂ (contract-rwst-∙?∙ Post pre m b o) =
    contract-rwst
      (λ x post outs →
        (safetyData1 : SafetyData) → x ≡ inj₂ safetyData1
        → RWST-weakestPre (m safetyData1) (RWST-Post++ Post outs) unit post)
      pre
      (λ { _ ()})
      λ { safetyData1 ._ refl → o safetyData1}

module ExtensionCheckM (voteProposal : VoteProposal) where
  postulate
    contract-∙?∙
      : ∀ {A} P pre {m : VoteData → LBFT (ErrLog ⊎ A)}
        → P (inj₁ unit) pre []
        → (∀ voteData → RWST-weakestPre (m voteData) P unit pre)
        → RWST-weakestPre (extensionCheckM voteProposal ∙?∙ m) P unit pre

module ConstructLedgerInfoM (proposedBlock : Block) (consensusDataHash : HashValue) where
  postulate
    contract
      : ∀ P pre
        → P (inj₁ unit) pre []
        → (∀ ledgerInfo → P (inj₂ ledgerInfo) pre [])
        → RWST-weakestPre (constructLedgerInfoM proposedBlock consensusDataHash) P unit pre

  contract-rwst-∙?∙
    : ∀ {A} P pre {m : LedgerInfo → LBFT (ErrLog ⊎ A)}
      → P (inj₁ unit) pre []
      → (∀ ledgerInfo → RWST-weakestPre (m ledgerInfo) P unit pre)
      → RWST-weakestPre (constructLedgerInfoM proposedBlock consensusDataHash ∙?∙ m) P unit pre
  proj₁ (contract-rwst-∙?∙ Post pre {m} b o) = contract _ pre (λ { unit _ → b }) λ { _ _ ()}
  proj₂ (contract-rwst-∙?∙ Post pre {m} b o) = contract _ pre (λ {_ ()}) (λ {li₁ .li₁ refl → o li₁})

module VerifyEpochM (epoch : Epoch) (safetyData : SafetyData) where
  contract-rwst-∙?∙
    : ∀ {A} P pre (m : Unit → LBFT (ErrLog ⊎ A))
      → P (inj₁ unit) pre []
      → RWST-weakestPre (m unit) P unit pre
      → RWST-weakestPre (verifyEpochM epoch safetyData ∙?∙ m) P unit pre
  proj₁ (proj₁ (contract-rwst-∙?∙ Post pre m b o)) _ unit _ = b
  proj₂ (proj₁ (contract-rwst-∙?∙ Post pre m b o)) _ _ ()
  proj₁ (proj₂ (contract-rwst-∙?∙ Post pre m b o)) _ _ ()
  proj₂ (proj₂ (contract-rwst-∙?∙ Post pre m b o)) _ unit _ = o


module VerifyAndUpdateLastVoteRoundM (round : Round) (safetyData : SafetyData) where
  C₁ = ⌊ round >? (safetyData ^∙ sdLastVotedRound) ⌋ ≡_
  safetyData≡ = (safetyData [ sdLastVotedRound := round ]) ≡_

  contract
    : ∀ P pre
      → (C₁ false → P (inj₁ unit) pre [])
      → (C₁ true → (safetyData1 : SafetyData) → safetyData≡ safetyData1
         → P (inj₂ safetyData1) pre [])
      → RWST-weakestPre (verifyAndUpdateLastVoteRoundM round safetyData) P unit pre
  proj₁ (contract P₁ pre b o) c₁t = o c₁t _ refl
  proj₂ (contract P₁ pre b o) c₁f = b c₁f

  contract-rwst
    : ∀ P pre
      → P (inj₁ unit) pre []
      → (∀ safetyData1 → P (inj₂ safetyData1) pre [])
      → RWST-weakestPre (verifyAndUpdateLastVoteRoundM round safetyData) P unit pre
  contract-rwst Post pre b o = contract Post pre (λ _ → b) λ _ safetyData _ → o safetyData

  contract-∙?∙
    : ∀ {A : Set} P pre {m : SafetyData → LBFT (ErrLog ⊎ A)}
      → (C₁ false → P (inj₁ unit) pre [])
      → (C₁ true
         → (safetyData1 : SafetyData) → safetyData≡ safetyData1
         → RWST-weakestPre (m safetyData1) P unit pre)
      → RWST-weakestPre (verifyAndUpdateLastVoteRoundM round safetyData ∙?∙ m) P unit pre
  proj₁ (proj₁ (contract-∙?∙ Post pre {m} b o)) _ _ ()
  proj₂ (proj₁ (contract-∙?∙ Post pre {m} b o)) c₁f unit _ = b c₁f
  proj₁ (proj₂ (contract-∙?∙ Post pre {m} b o)) c₁t ._ refl = o c₁t _ refl
  proj₂ (proj₂ (contract-∙?∙ Post pre {m} b o)) _ _ ()

module VerifyQcM (qc : QuorumCert) where
  postulate
    -- TODO-2: needs refining, when verifyQcM is implemented
    contract
      : ∀ P pre
        → (P (inj₁ unit) pre [])
        → (P (inj₂ unit) pre [])
        → RWST-weakestPre (verifyQcM qc) P unit pre

    contract-rwst-∙?∙
      : ∀ {A} P pre {m : LBFT (ErrLog ⊎ A)}
        → P (inj₁ unit) pre []
        → (RWST-weakestPre m P unit pre)
        → RWST-weakestPre (verifyQcM qc ∙?∙ λ _ → m) P unit pre

module ConstructAndSignVoteM where
  VoteSrcCorrect₁₂ : LBFT-Post (ErrLog ⊎ MetaVote)
  VoteSrcCorrect₁₂ (inj₁ _) post outs = Unit
  VoteSrcCorrect₁₂ (inj₂ v) post outs = v ^∙ mvSrc ≡ mvsNew

  module Continue2
    (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner) (proposedBlock : Block)
    (safetyData : SafetyData)
    where

    round  = proposedBlock ^∙ bBlockData ∙ bdRound
    author = validatorSigner ^∙ vsAuthor
    lastVotedRound = safetyData ^∙ sdLastVotedRound

    C₁ = ⌊ round >? lastVotedRound ⌋ ≡_

    c₃ : SafetyData → VoteData → Author → LedgerInfo → LBFT (ErrLog ⊎ MetaVote)
    c₃ safetyData1 voteData author ledgerInfo = do
      let signature = ValidatorSigner.sign ⦃ obm-dangerous-magic! ⦄ validatorSigner ledgerInfo
          vote      = Vote.newWithSignature voteData author ledgerInfo signature
      lSafetyData ∙= (safetyData1 [ sdLastVote ?= vote ])
      ok (MetaVote∙new vote mvsNew)

    c₂ : SafetyData → VoteData → LBFT (ErrLog ⊎ MetaVote)
    c₂ safetyData1 voteData = do
      let author = validatorSigner ^∙ vsAuthor
      constructLedgerInfoM proposedBlock (Crypto.hashVD voteData) ∙?∙ λ ledgerInfo → do
        c₃ safetyData1 voteData author ledgerInfo

    c₁ : SafetyData → LBFT (ErrLog ⊎ MetaVote)
    c₁ safetyData1 = do
      lSafetyData ∙= safetyData1
      extensionCheckM voteProposal ∙?∙ λ voteData → do
        c₂ safetyData1 voteData

    voteSrcCorrect
      : ∀ pre
        → RWST-weakestPre
            (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock safetyData)
            VoteSrcCorrect₁₂ unit pre
    voteSrcCorrect pre =
      VerifyAndUpdateLastVoteRoundM.contract-∙?∙ round safetyData
        VoteSrcCorrect₁₂ pre {m = c₁}
        (λ _ → unit)
        λ _ safetyData1 _ →
          let st₁ = pre [ lSafetyData := safetyData1 ] in
          ExtensionCheckM.contract-∙?∙ voteProposal VoteSrcCorrect₁₂ st₁
           {m = c₂ safetyData1}
           unit
           λ voteData →
             let author = validatorSigner ^∙ vsAuthor in
             ConstructLedgerInfoM.contract-rwst-∙?∙ proposedBlock (Crypto.hashVD voteData)
               VoteSrcCorrect₁₂ st₁
               {m = c₃ safetyData1 voteData author}
               unit
               λ ledgerInfo → refl

  module Continue1
    (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner) (proposedBlock : Block)
    (safetyData0 : SafetyData)
    where

    c₃ : Unit → LBFT (ErrLog ⊎ MetaVote)
    c₃ _ =
      verifyAndUpdatePreferredRoundM (proposedBlock ^∙ bQuorumCert) safetyData0 ∙?∙
        constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock

    c₂ : ValidatorVerifier → LBFT (ErrLog ⊎ MetaVote)
    c₂ validatorVerifier =
      pure (Block.validateSignature proposedBlock validatorVerifier) ∙?∙
        c₃

    c₁ : LBFT (ErrLog ⊎ MetaVote)
    c₁ = do
      validatorVerifier ← gets rmGetValidatorVerifier
      c₂ validatorVerifier

    voteSrcCorrect
      : ∀ pre
        → RWST-weakestPre
          (constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0)
          VoteSrcCorrect₁₂ unit pre
    voteSrcCorrect pre =
      VerifyQcM.contract-rwst-∙?∙ (proposedBlock ^∙ bQuorumCert) VoteSrcCorrect₁₂ pre
        {m = c₁} unit
        ((λ _ _ → unit)
        , λ {unit _ →
          VerifyAndUpdatePreferredRoundM.contract-rwst-∙?∙
            (proposedBlock ^∙ bQuorumCert) safetyData0 VoteSrcCorrect₁₂
            pre (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock)
            unit
            (λ safetyData1 →
              Continue2.voteSrcCorrect voteProposal validatorSigner proposedBlock safetyData1 pre)})

  VoteSrcCorrect : RoundManager → LBFT-Post (ErrLog ⊎ MetaVote)
  VoteSrcCorrect pre e@(inj₁ x) post outs =
    VoteSrcCorrect₁₂ e post outs
  VoteSrcCorrect pre mv@(inj₂ (MetaVote∙new ₋mvVote mvsNew)) post outs =
    VoteSrcCorrect₁₂ mv post outs
  VoteSrcCorrect pre (inj₂ (MetaVote∙new v mvsLastVote)) post outs =
    just v ≡ (pre ^∙ lSafetyData ∙ sdLastVote)


  module Continue0 (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner) where

    c₁ : Block → SafetyData → LBFT (ErrLog ⊎ MetaVote)
    c₁ proposedBlock safetyData0 = do
      caseMM (safetyData0 ^∙ sdLastVote) of λ where
        (just vote) →
          ifM (vote ^∙ vVoteData ∙ vdProposed ∙ biRound) ≟ℕ (proposedBlock ^∙ bRound)
            then ok (MetaVote∙new vote mvsLastVote)
            else constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0
        nothing → constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0

    proposedBlock = voteProposal ^∙ vpBlock

    voteSrcCorrect
      : ∀ pre
        → RWST-weakestPre
            (constructAndSignVoteM-continue0 voteProposal validatorSigner)
            (VoteSrcCorrect pre) unit pre
    voteSrcCorrect pre =
      VerifyEpochM.contract-rwst-∙?∙ (proposedBlock ^∙ bEpoch) safetyData0 (VoteSrcCorrect pre) pre
        (λ _ → c₁ proposedBlock safetyData0)
        unit vsc₁
      where
      safetyData0 = pre ^∙ lSafetyData

      vsc₁ : RWST-weakestPre (c₁ proposedBlock safetyData0) (VoteSrcCorrect pre) unit pre
      proj₁ vsc₁ x =
        Continue1.voteSrcCorrect voteProposal validatorSigner proposedBlock safetyData0 pre
      proj₁ (proj₂ vsc₁ v lastVote) _ = sym lastVote
      proj₂ (proj₂ vsc₁ v lastVote) _ =
        Continue1.voteSrcCorrect voteProposal validatorSigner proposedBlock safetyData0 pre
