{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
import      LibraBFT.ImplShared.Util.Crypto                         as Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Impl.Types.ValidatorSigner               as ValidatorSigner
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
open import LibraBFT.Impl.Consensus.RoundManager.PropertyDefs
open import LibraBFT.Impl.Consensus.SafetyRules.SafetyRules

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
          → (C₂ true → P (inj₂ (safetyData & sdPreferredRound ∙~ twoChainRound)) pre [])
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

module ExtensionCheckM (voteProposal : VoteProposal) where
  postulate
    contract
      : ∀ P pre
        → P (inj₁ unit) pre []
        → (∀ voteData → P (inj₂ voteData) pre [])
        → RWST-weakestPre (extensionCheckM voteProposal) P unit pre

module ConstructLedgerInfoM (proposedBlock : Block) (consensusDataHash : HashValue) where
  postulate
    contract
      : ∀ P pre
        → P (inj₁ unit) pre []
        → (∀ ledgerInfo → P (inj₂ ledgerInfo) pre [])
        → RWST-weakestPre (constructLedgerInfoM proposedBlock consensusDataHash) P unit pre

module VerifyEpochM (epoch : Epoch) (safetyData : SafetyData) where
  contract
    : ∀ P pre
      → P (inj₁ unit) pre []
      → P (inj₂ unit) pre []
      → RWST-weakestPre (verifyEpochM epoch safetyData) P unit pre
  proj₁ (contract Post pre b o) _ = b
  proj₂ (contract Post pre b o) _ = o


module VerifyAndUpdateLastVoteRoundM (round : Round) (safetyData : SafetyData) where
  C₁ = ⌊ round >? (safetyData ^∙ sdLastVotedRound) ⌋ ≡_
  safetyData≡ = (safetyData & sdLastVotedRound ∙~ round) ≡_

  contract
    : ∀ P pre
      → (C₁ false → P (inj₁ unit) pre [])
      → (C₁ true → P (inj₂ (safetyData & sdLastVotedRound ∙~ round)) pre [])
      → RWST-weakestPre (verifyAndUpdateLastVoteRoundM round safetyData) P unit pre
  proj₁ (contract P₁ pre b o) c₁t = o c₁t
  proj₂ (contract P₁ pre b o) c₁f = b c₁f

module VerifyQcM (qc : QuorumCert) where
  postulate
    -- TODO-2: needs refining, when verifyQcM is implemented
    contract
      : ∀ P pre
        → (P (inj₁ unit) pre [])
        → (P (inj₂ unit) pre [])
        → RWST-weakestPre (verifyQcM qc) P unit pre

module ConstructAndSignVoteM where
  VoteSrcCorrect : RoundManager → (ErrLog ⊎ VoteWithMeta) → RoundManager → Set
  VoteSrcCorrect pre (inj₁ _) post = Unit
  VoteSrcCorrect pre (inj₂ mv) post = VoteSrcCorrectCod pre post mv

  record Contract (pre : RoundManager) (r : ErrLog ⊎ VoteWithMeta) (post : RoundManager) (outs : List Output) : Set where
    field
      noOutput       : outs ≡ []
      voteSrcCorrect : VoteSrcCorrect pre r post

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
      let signature = ValidatorSigner.sign validatorSigner ledgerInfo
          vote      = Vote.newWithSignature voteData author ledgerInfo signature
      lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)
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

    contract
      : ∀ pre
        → RWST-weakestPre
            (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock safetyData)
            (Contract pre) unit pre
    contract pre =
      VerifyAndUpdateLastVoteRoundM.contract round safetyData
        (RWST-weakestPre-ebindPost unit c₁ (Contract pre)) pre
        (λ _ → record { noOutput = refl ; voteSrcCorrect = unit })
        λ _ safetyData1 safetyData1≡ → λ where
          ._ refl unit _ →
            let st₁ = pre & lSafetyData ∙~ safetyData1 in
            ExtensionCheckM.contract voteProposal
              (RWST-weakestPre-ebindPost unit (c₂ safetyData1) _) st₁
              (record { noOutput = refl ; voteSrcCorrect = unit })
              λ _ voteData _ →
                ConstructLedgerInfoM.contract proposedBlock (Crypto.hashVD voteData)
                  (RWST-weakestPre-ebindPost _ (c₃ safetyData1 voteData author) _) st₁
                  (record { noOutput = refl ; voteSrcCorrect = unit })
                  (λ _ ledgerInfo _ → λ _ _ _ _ →
                    record { noOutput = refl ; voteSrcCorrect = refl })

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

    contract
      : ∀ pre
        → RWST-weakestPre
            (constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0)
            (Contract pre) unit pre
    contract pre =
      VerifyQcM.contract (proposedBlock ^∙ bQuorumCert)
        (RWST-weakestPre-ebindPost unit (λ _ → c₁) _) pre
        (record { noOutput = refl ; voteSrcCorrect = unit })
        λ where
          unit _ validatorVerifier vv≡ →
            either{C = λ x → RWST-weakestPre (pure x ∙?∙ c₃) (Contract pre) _ _}
              (λ _ → record { noOutput = refl ; voteSrcCorrect = unit })
              (λ where
                unit unit _ →
                  VerifyAndUpdatePreferredRoundM.contract (proposedBlock ^∙ bQuorumCert) safetyData0
                    (RWST-weakestPre-ebindPost unit (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock) _)
                    pre
                    (λ _ → record { noOutput = refl ; voteSrcCorrect = unit })
                    λ _ →
                      -- Though this appears repetitive now, in the future the
                      -- contract will likely be refined to consider when and
                      -- how the preferred round is updated.
                      (λ twoChainRound>preferredRound safetyData1 safetyData1≡ →
                        Continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre)
                      , (λ twoChainRound<preferredRound safetyData1 safetyData1≡ →
                           Continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre)
                      , λ twoChainRound=preferredRound safetyData1 safetyData1≡ →
                          Continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre)
              (Block.validateSignature proposedBlock validatorVerifier)

  module Continue0 (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner) where

    proposedBlock = voteProposal ^∙ vpBlock

    c₁ : SafetyData → LBFT (ErrLog ⊎ VoteWithMeta)
    c₁ safetyData0 = do
      caseMM (safetyData0 ^∙ sdLastVote) of λ where
        (just vote) →
          ifM (vote ^∙ vVoteData ∙ vdProposed ∙ biRound) ≟ℕ (proposedBlock ^∙ bRound)
            then ok (VoteWithMeta∙new vote mvsLastVote)
            else constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0
        nothing → constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0

    contract
      : ∀ pre
        → RWST-weakestPre (constructAndSignVoteM-continue0 voteProposal validatorSigner)
            (Contract pre) unit pre
    proj₁ (contract pre safetyData0@._ refl) c₁≡true = record { noOutput = refl ; voteSrcCorrect = unit }
    proj₁ (proj₂ (contract pre safetyData0@._ refl) c₁≡false unit _) ≡nothing =
      Continue1.contract voteProposal validatorSigner proposedBlock safetyData0 pre
    proj₁ (proj₂ (proj₂ (contract pre safetyData0@._ refl) c₁≡false unit _) j j≡) c₂≡true =
      record { noOutput = refl ; voteSrcCorrect = sym j≡ , refl }
    proj₂ (proj₂ (proj₂ (contract pre safetyData0@._ refl) c₁≡false unit _) j j≡) c₂≡false =
      Continue1.contract voteProposal validatorSigner proposedBlock safetyData0 pre

  module _ (maybeSignedVoteProposal : MaybeSignedVoteProposal) where

    voteProposal = maybeSignedVoteProposal ^∙ msvpVoteProposal

    contract : ∀ pre → RWST-weakestPre (constructAndSignVoteM maybeSignedVoteProposal) (Contract pre) unit pre
    proj₁ (contract pre vs vs≡) vs≡nothing = record { noOutput = refl ; voteSrcCorrect = unit }
    proj₂ (contract pre vs vs≡) j j≡ = Continue0.contract voteProposal j pre

    contract⇒ : ∀ pre Post
                → (∀ r st outs → Contract pre r st outs → Post r st outs)
                → RWST-weakestPre (constructAndSignVoteM maybeSignedVoteProposal) Post unit pre
    contract⇒ pre Post impl =
      RWST-impl (Contract pre) Post impl
        (constructAndSignVoteM maybeSignedVoteProposal) unit pre
        (contract pre)
