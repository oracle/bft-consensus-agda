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
open import LibraBFT.Impl.Consensus.RoundManager.PropertyDefs
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

  postulate
    contract
      : ∀ P pre
        → (C₁ true → P (inj₁ unit) pre [])
        → (C₁ false
          → (C₂ true → P (inj₂ (safetyData [ sdPreferredRound := twoChainRound ])) pre [])
            × (C₃ true → P (inj₂ safetyData) pre [])
            × (C₄ true → P (inj₂ safetyData) pre []))
        → RWST-weakestPre (verifyAndUpdatePreferredRoundM quorumCert safetyData) P unit pre

  -- proj₁ (contract P₁ pre b o) = b
  -- proj₁ (proj₂ (contract P₁ pre b o) c₁f) c₂t = proj₁ (o c₁f) c₂t
  -- proj₁ (proj₂ (proj₂ (contract P₁ pre b o) c₁f) c₂f) c₃t = proj₁ (proj₂ (o c₁f)) c₃t
  -- proj₂ (proj₂ (proj₂ (contract P₁ pre b o) c₁f) c₂f) c₃f
  --   with twoChainRound ≟ preferredRound
  -- ...| yes proof = proj₂ (proj₂ (o c₁f)) refl
  -- ...| no  proof
  --    with twoChainRound >? preferredRound
  --    |    twoChainRound <? preferredRound
  -- ...| no pf₁ | no pf₂
  --    with <-cmp twoChainRound preferredRound
  -- ... | tri< imp _ _ = ⊥-elim (pf₂ imp)
  -- ... | tri≈ _ imp _ = ⊥-elim (proof imp)
  -- ... | tri> _ _ imp = ⊥-elim (pf₁ imp)

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

module ExtensionCheckM (voteProposal : VoteProposal) where
  postulate
    contract
      : ∀ P pre
        → P (inj₁ unit) pre []
        → (∀ voteData → P (inj₂ voteData) pre [])
        → RWST-weakestPre (extensionCheckM voteProposal) P unit pre

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
  contract-rwst-∙?∙ Post pre {m} b o =
    contract (RWST-weakestPre-ebindPost unit m Post) pre
      b λ {ledgerInfo ._ refl → o ledgerInfo}

module VerifyEpochM (epoch : Epoch) (safetyData : SafetyData) where
  contract-rwst
    : ∀ P pre
      → P (inj₁ unit) pre []
      → P (inj₂ unit) pre []
      → RWST-weakestPre (verifyEpochM epoch safetyData) P unit pre
  proj₁ (contract-rwst Post pre b o) _ = b
  proj₂ (contract-rwst Post pre b o) _ = o


module VerifyAndUpdateLastVoteRoundM (round : Round) (safetyData : SafetyData) where
  C₁ = ⌊ round >? (safetyData ^∙ sdLastVotedRound) ⌋ ≡_
  safetyData≡ = (safetyData [ sdLastVotedRound := round ]) ≡_

  contract
    : ∀ P pre
      → (C₁ false → P (inj₁ unit) pre [])
      → (C₁ true → P (inj₂ (safetyData [ sdLastVotedRound := round ])) pre [])
      → RWST-weakestPre (verifyAndUpdateLastVoteRoundM round safetyData) P unit pre
  proj₁ (contract P₁ pre b o) c₁t = o c₁t
  proj₂ (contract P₁ pre b o) c₁f = b c₁f

  contract-rwst
    : ∀ P pre
      → P (inj₁ unit) pre []
      → (∀ safetyData1 → P (inj₂ safetyData1) pre [])
      → RWST-weakestPre (verifyAndUpdateLastVoteRoundM round safetyData) P unit pre
  contract-rwst Post pre b o = contract Post pre (λ _ → b) λ _ → o _

module VerifyQcM (qc : QuorumCert) where
  postulate
    -- TODO-2: needs refining, when verifyQcM is implemented
    contract-rwst
      : ∀ P pre
        → (P (inj₁ unit) pre [])
        → (P (inj₂ unit) pre [])
        → RWST-weakestPre (verifyQcM qc) P unit pre

module ConstructAndSignVoteM where
  VoteSrcCorrect : RoundManager → LBFT-Post (ErrLog ⊎ VoteWithMeta)
  VoteSrcCorrect pre (inj₁ _) post outs = Unit
  VoteSrcCorrect pre (inj₂ mv) post outs = VoteSrcCorrectCod pre post mv

  module Continue2
    (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner) (proposedBlock : Block)
    (safetyData : SafetyData)
    where

    round  = proposedBlock ^∙ bBlockData ∙ bdRound
    author = validatorSigner ^∙ vsAuthor
    lastVotedRound = safetyData ^∙ sdLastVotedRound

    C₁ = ⌊ round >? lastVotedRound ⌋ ≡_

    c₃ : SafetyData → VoteData → Author → LedgerInfo → LBFT (ErrLog ⊎ VoteWithMeta)
    c₃ safetyData1 voteData author ledgerInfo = do
      let signature = ValidatorSigner.sign ⦃ obm-dangerous-magic! ⦄ validatorSigner ledgerInfo
          vote      = Vote.newWithSignature voteData author ledgerInfo signature
      lSafetyData ∙= (safetyData1 [ sdLastVote ?= vote ])
      ok (VoteWithMeta∙new vote mvsNew)

    c₂ : SafetyData → VoteData → LBFT (ErrLog ⊎ VoteWithMeta)
    c₂ safetyData1 voteData = do
      let author = validatorSigner ^∙ vsAuthor
      constructLedgerInfoM proposedBlock (Crypto.hashVD voteData) ∙?∙ λ ledgerInfo → do
        c₃ safetyData1 voteData author ledgerInfo

    c₁ : SafetyData → LBFT (ErrLog ⊎ VoteWithMeta)
    c₁ safetyData1 = do
      lSafetyData ∙= safetyData1
      extensionCheckM voteProposal ∙?∙ λ voteData → do
        c₂ safetyData1 voteData

    voteSrcCorrect
      : ∀ rm pre
        → RWST-weakestPre
            (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock safetyData)
            (VoteSrcCorrect rm) unit pre
    voteSrcCorrect rm pre =
      VerifyAndUpdateLastVoteRoundM.contract round safetyData
        (RWST-weakestPre-ebindPost unit c₁ (VoteSrcCorrect rm)) pre
        (λ _ → unit)
        λ _ safetyData1 safetyData1≡ → λ where
          ._ refl unit _ →
            let st₁ = pre [ lSafetyData := safetyData1 ] in
            ExtensionCheckM.contract voteProposal (RWST-weakestPre-ebindPost unit (c₂ safetyData1) _) st₁
              unit
              λ _ voteData _ →
                ConstructLedgerInfoM.contract proposedBlock (Crypto.hashVD voteData)
                  (RWST-weakestPre-ebindPost _ (c₃ safetyData1 voteData author) _) st₁
                  unit
                  λ _ ledgerInfo _ → λ _ _ _ _ → refl

  module Continue1
    (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner) (proposedBlock : Block)
    (safetyData0 : SafetyData)
    where

    c₃ : Unit → LBFT (ErrLog ⊎ VoteWithMeta)
    c₃ _ =
      verifyAndUpdatePreferredRoundM (proposedBlock ^∙ bQuorumCert) safetyData0 ∙?∙
        constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock

    c₂ : ValidatorVerifier → LBFT (ErrLog ⊎ VoteWithMeta)
    c₂ validatorVerifier =
      pure (Block.validateSignature proposedBlock validatorVerifier) ∙?∙
        c₃

    c₁ : LBFT (ErrLog ⊎ VoteWithMeta)
    c₁ = do
      validatorVerifier ← gets rmGetValidatorVerifier
      c₂ validatorVerifier

    voteSrcCorrect
      : ∀ rm pre
        → RWST-weakestPre
          (constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0)
          (VoteSrcCorrect rm) unit pre
    voteSrcCorrect rm pre =
      VerifyQcM.contract-rwst (proposedBlock ^∙ bQuorumCert)
        (RWST-weakestPre-ebindPost unit (λ _ → c₁) _) pre unit λ where
          unit _ ._ refl → λ validatorVerifier vv≡ →
            either {C = λ x → RWST-weakestPre (pure x ∙?∙ c₃) (VoteSrcCorrect rm) _ _}
              (const unit)
              (λ _ _ _ →
                VerifyAndUpdatePreferredRoundM.contract-rwst (proposedBlock ^∙ bQuorumCert) safetyData0
                  (RWST-weakestPre-ebindPost unit
                     (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock)
                     _)
                  pre unit
                  λ _ safetyData1 _ →
                    Continue2.voteSrcCorrect voteProposal validatorSigner proposedBlock safetyData1 rm pre)
              (Block.validateSignature proposedBlock validatorVerifier)

  module Continue0 (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner) where

    c₁ : Block → SafetyData → LBFT (ErrLog ⊎ VoteWithMeta)
    c₁ proposedBlock safetyData0 = do
      caseMM (safetyData0 ^∙ sdLastVote) of λ where
        (just vote) →
          ifM (vote ^∙ vVoteData ∙ vdProposed ∙ biRound) ≟ℕ (proposedBlock ^∙ bRound)
            then ok (VoteWithMeta∙new vote mvsLastVote)
            else constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0
        nothing → constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0

    proposedBlock = voteProposal ^∙ vpBlock

    voteSrcCorrect
      : ∀ rm pre → rm ≡L pre at (lSafetyData ∙ sdLastVote)
        → RWST-weakestPre
            (constructAndSignVoteM-continue0 voteProposal validatorSigner)
            (VoteSrcCorrect rm) unit pre
    proj₁ (voteSrcCorrect rm pre pf _ refl safetyData0 safetyData0≡) _ = unit
    proj₁ (proj₂ (voteSrcCorrect rm pre pf _ refl safetyData0 safetyData0≡) _ unit _) ≡nothing
      = Continue1.voteSrcCorrect voteProposal validatorSigner proposedBlock safetyData0 rm pre
    proj₁ (proj₂ (proj₂ (voteSrcCorrect rm pre pf _ refl safetyData0@_ safetyData0≡) _ unit _) _ refl) _
      rewrite pf = cong (_^∙ sdLastVote) safetyData0≡
    proj₂ (proj₂ (proj₂ (voteSrcCorrect rm pre pf _ refl safetyData0@_ safetyData0≡) _ unit _) _ refl) _
      = Continue1.voteSrcCorrect voteProposal validatorSigner proposedBlock safetyData0 rm pre

  module _ (maybeSignedVoteProposal : MaybeSignedVoteProposal) where

    -- TODO-2: This should be be proved "by construction", not separately
    postulate
      contract-noOuts
        : ∀ P pre
          → (∀ x st → P x st [])
          → RWST-weakestPre (constructAndSignVoteM maybeSignedVoteProposal) P unit pre

    voteProposal = maybeSignedVoteProposal ^∙ msvpVoteProposal

    voteSrcCorrect
      : ∀ rm pre → rm ≡L pre at (lSafetyData ∙ sdLastVote)
        → RWST-weakestPre
          (constructAndSignVoteM maybeSignedVoteProposal)
          (VoteSrcCorrect rm) unit pre
    proj₁ (voteSrcCorrect rm pre pf _ refl vs vs≡) ≡nothing = unit
    proj₂ (voteSrcCorrect rm pre pf _ refl vs vs≡) validatorSigner validatorSigner≡ =
      Continue0.voteSrcCorrect voteProposal validatorSigner rm pre pf
