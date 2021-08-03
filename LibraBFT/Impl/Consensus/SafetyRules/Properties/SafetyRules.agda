{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Base.KVMap                               as Map
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.Hash
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.Properties.QuorumCert as QuorumCertProps
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteData   as VoteData
import      LibraBFT.Impl.Consensus.ConsensusTypes.Properties.VoteData as VoteDataProps
open import LibraBFT.Impl.Consensus.SafetyRules.SafetyRules
open import LibraBFT.Impl.Handle
open import LibraBFT.Impl.Properties.Util
open import LibraBFT.Impl.OBM.Crypto                          as Crypto
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.LedgerInfoWithSignatures      as LedgerInfoWithSignatures
open import LibraBFT.Impl.Types.ValidatorSigner               as ValidatorSigner
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
import      LibraBFT.ImplShared.Util.Crypto                   as Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Lemmas
open import LibraBFT.Prelude

open        ParamsWithInitAndHandlers InitAndHandlers
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms InitAndHandlers PeerCanSignForPK PeerCanSignForPK-stable
open RoundManagerInvariants
open RoundManagerTransProps

module LibraBFT.Impl.Consensus.SafetyRules.Properties.SafetyRules where

module verifyAndUpdatePreferredRoundDefs (quorumCert : QuorumCert) (safetyData : SafetyData) where
  preferredRound = safetyData ^∙ sdPreferredRound
  oneChainRound  = quorumCert ^∙ qcCertifiedBlock ∙ biRound
  twoChainRound  = quorumCert ^∙ qcParentBlock ∙ biRound

  C₁ = oneChainRound < preferredRound
  C₂ = twoChainRound > preferredRound
  C₃ = twoChainRound < preferredRound
  C₄ = twoChainRound ≡ preferredRound

  safetyData' = safetyData & sdPreferredRound ∙~ twoChainRound

module verifyAndUpdatePreferredRoundMSpec (quorumCert : QuorumCert) (safetyData : SafetyData) where
  open verifyAndUpdatePreferredRoundDefs quorumCert safetyData

  module _ (pre : RoundManager) where
    record setPR (sd : SafetyData) : Set where
      field
        cond  : C₂
        eff   : sd ≡ safetyData'

    record noChanges (sd : SafetyData) : Set where
      field
        noUpd : sd ≡ safetyData

    record ConditionCorrectR (sd : SafetyData) : Set where
      field
        ep≡    : sd ≡L safetyData at sdEpoch
        qcr≤pr : quorumCert ^∙ qcParentBlock ∙ biRound ≤ sd ^∙ sdPreferredRound
        conds  : noChanges sd ⊎ setPR sd
    open ConditionCorrectR public

    ConditionCorrect : Either ErrLog SafetyData → Set
    ConditionCorrect (Left _)   = ⊤
    ConditionCorrect (Right sd) = ConditionCorrectR sd

    record Contract (r : Either ErrLog SafetyData) (post : RoundManager) (outs : List Output) : Set where
      constructor mkContract
      field
        noOuts        : OutputProps.NoMsgs outs
        noEff         : post ≡ pre
        condCorr      : ConditionCorrect r

  contract
      : ∀ pre
        → LBFT-weakestPre (verifyAndUpdatePreferredRoundM quorumCert safetyData)
                          (Contract pre) pre
  proj₁ (contract pre) _ = mkContract refl refl tt
  proj₂ (contract pre) x rewrite x
     with <-cmp twoChainRound preferredRound
  ...| tri< lt _   _  = λ where ._ refl ._ refl → mkContract refl refl
                                                    (record { ep≡ = refl
                                                            ; qcr≤pr = <⇒≤ lt
                                                            ; conds = inj₁ (record { noUpd = refl }) })
  ...| tri≈ _ refl _  = λ where ._ refl         → mkContract refl refl
                                                    (record { ep≡ = refl
                                                            ; qcr≤pr = ≤-refl
                                                            ; conds = inj₁ (record { noUpd = refl }) })
  ...| tri> _ _    gt = λ where ._ refl ._ refl → mkContract refl refl
                                                    (record { ep≡ = refl
                                                            ; qcr≤pr = ≤-refl
                                                            ; conds = inj₂ (record { cond = gt ; eff = refl }) })

module extensionCheckSpec (voteProposal : VoteProposal) where
  proposedBlock = voteProposal ^∙ vpBlock
  obmAEP        = voteProposal ^∙ vpAccumulatorExtensionProof

  voteData      =
     (VoteData.new
       (Block.genBlockInfo
         proposedBlock
         -- OBM-LBFT-DIFF: completely different
         (Crypto.obmHashVersion (obmAEP ^∙ aepObmNumLeaves))
         (obmAEP ^∙ aepObmNumLeaves)
         (voteProposal ^∙ vpNextEpochState))
       (proposedBlock ^∙ bQuorumCert ∙ qcCertifiedBlock))

  contract -- TODO-1: refine (waiting on: extensionCheckM)
    : ∀ {ℓ} (Post : Either ErrLog VoteData → Set ℓ)
      → (∀ e → Post (Left e))
      → (Post (pure voteData))
      → Post (extensionCheck voteProposal)
  contract Post pfBail pfOk = pfOk

module constructLedgerInfoMSpec (proposedBlock : Block) (consensusDataHash : HashValue) where
  -- This is a place-holder contract that requires refinement once
  -- `constructLedgerInfoM is implemented.
  postulate -- TODO-1: refine and prove
    contract
      : ∀ P pre
        → P (inj₁ fakeErr) pre []
        → (∀ ledgerInfo → P (inj₂ ledgerInfo) pre [])
        → LBFT-weakestPre (constructLedgerInfoM proposedBlock consensusDataHash) P pre

-- TUTORIAL: Weakest preconditions generated from conditionals, translating a
-- boolean equality test to proofs of (in)equality.
module verifyEpochMSpec (epoch : Epoch) (safetyData : SafetyData) where
  -- The body of `verifyEpochM` is:
  -- > ifM not ⌊ epoch ≟ℕ safetyData ^∙ sdEpoch ⌋
  -- >   then bail fakeErr -- log: error: incorrect epoch
  -- >   else ok unit
  contract
    : ∀ P pre
      → (epoch ≢ safetyData ^∙ sdEpoch → P (inj₁ fakeErr) pre [])
      → (epoch ≡ safetyData ^∙ sdEpoch → P (inj₂ unit) pre [])
      → LBFT-weakestPre (verifyEpochM epoch safetyData) P pre
  -- The outermost node of the AST of `verifyEpochM` is `ifM_then_else_ ...`, so
  -- our goal is to return a product: one proof corresponding to the "then" case
  -- one and one proof corresponding to the "else" case.
  --
  -- 1. In the "then" case, we recieve a proof `e≢` that
  --    > toBool (not ⌊ epoch ≟ℕ safetyData ^∙ sdEpoch ⌋) ≡ true
  proj₁ (contract Post pre pfBail pfOk) e≢
  --    - abstract over the expression that prevents us from analyzing this evidence
     with epoch ≟ℕ safetyData ^∙ sdEpoch
  --    - Agda can tell that `yes pf` is not an option, since e≢ would have type
  --      `false ≡ true` in that case
  ...| no  pf = pfBail pf
  -- 2. In the "else" case, we receive a proof `e≡` that
  --    > toBool (not ⌊ epoch ≟ℕ safetyData ^∙ sdEpoch ⌋) ≡ false
  proj₂ (contract Post pre pfBail pfOk) e≡
  --    - perform the same `with` abstraction as the previous case
     with epoch ≟ℕ safetyData ^∙ sdEpoch
  --    - Agda can tell that `no pf` is not an option
  ...| yes pf = pfOk pf


-- TUTORIAL: Translating boolean comparison tests to proofs.
module verifyAndUpdateLastVoteRoundMSpec (round : Round) (safetyData : SafetyData) where
  safetyData' = safetyData & sdLastVotedRound ∙~ round
  -- This example shows that we could have further simplified the proof of the
  -- contract for `verifyEpochM`. In `LibraBFT.Prelude`, we define lemmas
  -- > toWitnessT : ∀{ℓ}{P : Set ℓ}{d : Dec P} → ⌊ d ⌋ ≡ true → P
  -- > toWitnessF : ∀{ℓ}{P : Set ℓ}{d : Dec P} → ⌊ d ⌋ ≡ false → ¬ P
  -- which extract the underlying proof used to construct `d` given evidence
  -- that "lowering" `d` to a boolean produces `true` or `false`.
  contract
    : ∀ P pre
      → ((r>lvr : round > safetyData ^∙ sdLastVotedRound) → P (Right safetyData') pre [])
      → ((r≤lvr : ¬ (round > safetyData ^∙ sdLastVotedRound)) → P (Left fakeErr) pre [])
      → LBFT-weakestPre (verifyAndUpdateLastVoteRoundM round safetyData) P pre
  proj₁ (contract Post pre pfOk pfBail) r>lvr = pfOk (toWitnessT r>lvr)
  proj₂ (contract Post pre pfOk pfBail) ¬r>lvr = pfBail (toWitnessF ¬r>lvr)


module verifyQcMSpec (self : QuorumCert) where
  getVv : RoundManager → ValidatorVerifier
  getVv = _^∙ (rmEpochState ∙ esVerifier)

  -- See comment on contract below to understand the motivation for stating and proving the property
  -- this way.

  Contract : RoundManager → RWST-Post Output RoundManager (Either ErrLog Unit)
  Contract pre (Left _)  post outs = post ≡ pre × outs ≡ []
  Contract pre (Right _) post outs = post ≡ pre × outs ≡ []
                                   × QuorumCertProps.Contract self (getVv pre)

  contract' : ∀ pre → RWST-weakestPre (verifyQcM self) (Contract pre) unit pre
  contract' pre _vv ._
     with self ^∙ qcSignedLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash ≟ hashVD (self ^∙ qcVoteData)
  ...| no neq = λ where _ refl → refl , refl
  ...| yes refl
     with self ^∙ qcCertifiedBlock ∙ biRound ≟ 0
  ...| yes refl
     with self ^∙ qcParentBlock ≟ self ^∙ qcCertifiedBlock
  ...| no neq = λ where _ refl → refl , refl
  ...| yes refl
     with self ^∙ qcCertifiedBlock ≟ self ^∙ qcLedgerInfo ∙ liwsLedgerInfo ∙ liCommitInfo
  ...| no neq = λ where _ refl → refl , refl
  ...| yes refl
     with Map.kvm-size (self ^∙ qcLedgerInfo ∙ liwsSignatures) ≟ 0
  ...| no neq = λ where _ refl → refl , refl
  ...| yes noSigs =
         λ where _ refl →
                  refl , refl , record { lihash≡ = refl
                                       ; rnd≟0 = yes refl
                                       ; parProp = record { par≡cert = refl
                                                          ; cert≡li = refl
                                                          ; noSigs = noSigs } }
  contract' pre vv refl
     | yes refl
     | no neq
     with  LedgerInfoWithSignatures.verifySignatures (self ^∙ qcLedgerInfo)  vv | inspect
          (LedgerInfoWithSignatures.verifySignatures (self ^∙ qcLedgerInfo)) vv
  ...| Left e     | _ = λ where _ refl → refl , refl
  ...| Right unit | [ R ]
     with VoteData.verify (self ^∙ qcVoteData) | inspect
          VoteData.verify (self ^∙ qcVoteData)
  ...| Left e     | _ = λ where _ refl → refl , refl
  ...| Right unit | [ R' ] =
         λ where _ refl →
                  refl , refl , record { lihash≡ = refl
                                       ; rnd≟0   = no neq
                                       ; parProp = record { sigProp = R
                                                          ; vdProp = VoteDataProps.contract
                                                                       (self ^∙ qcVoteData)
                                                                       R' }}

  -- Suppose verifyQcM runs from prestate pre, and we wish to ensure that postcondition Post holds
  -- afterwards.  If P holds provided verifyQcM does not modify the state and does not produce any
  -- Outputs, and, if verifyQcM succeeds (returns Right unit), P holds provided
  -- QuorumCertProps.Contract holds for the given QuorumCert and the ValidatorVerifier of the
  -- prestate, then verifyQcM ensures P holds.  Proving this directly is painful because it's
  -- difficult to construct a QuorumCertProps.Contract self (getVv pre) that Agda understands allows
  -- us to invoke the rPrf (condition on P in case verifyQcM succeeds).  Therefore, we restate the
  -- conditions on P (as P', above) and prove that P' implies P, and then use LBFT-⇒ to achieve
  -- the desired result.
  contract
    : ∀ P pre
    → (∀ {e} → P (Left e) pre [])  -- verifyQcM does not emit any outputs, it just propagates a Left ErrLog, hence [] 
    → (QuorumCertProps.Contract self (getVv pre) → P (Right unit) pre [])
    → RWST-weakestPre (verifyQcM self) P unit pre
  contract Post pre lPrf rPrf = LBFT-⇒ (Contract pre) Post
                                       (λ { (Left x₁) st outs (refl , refl)          → lPrf
                                          ; (Right unit) st outs (refl , refl , prf) → rPrf prf })
                                       (verifyQcM self)
                                       pre
                                       (contract' pre)


module constructAndSignVoteMSpec where

  VoteResultCorrect : (pre post : RoundManager) (block : Block) (lvr≡? : Bool) (r : Either ErrLog Vote) → Set
  VoteResultCorrect pre post block lvr≡? (Left e) = VoteNotGenerated pre post lvr≡?
  VoteResultCorrect pre post block lvr≡? (Right vote) = Voting.VoteGeneratedCorrect pre post vote block

  record Contract (pre : RoundManager) (pool : SentMessages) (block : Block) (r : Either ErrLog Vote) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      -- General properties / invariants
      rmInv          : Preserves (RoundManagerInv pool) pre post
      noEpochChange  : NoEpochChange pre post
      noMsgOuts      : OutputProps.NoMsgs outs
      -- Voting
      lvr≡?          : Bool
      voteResCorrect : VoteResultCorrect pre post block lvr≡? r

  private
    contractBail : ∀ {pre pool block e} outs → OutputProps.NoMsgs outs → Contract pre pool block (Left e) pre outs
    contractBail{pre} outs noMsgs =
      mkContract
        reflPreservesRoundManagerInv
        (reflNoEpochChange{pre})
        noMsgs
        true reflVoteNotGenerated

  module continue2
    (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner)
    (proposedBlock : Block)       (safetyData : SafetyData) where

    open constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock safetyData

    record Requirements (pre : RoundManager) : Set where
      constructor mkRequirements
      field
        es≡₁  : (pre ^∙ pssSafetyData-rm) ≡L safetyData at sdEpoch
        es≡₂  : voteProposal ^∙ vpBlock ∙ bEpoch ≡ safetyData ^∙ sdEpoch
        lv≡  : (pre ^∙ pssSafetyData-rm) ≡L safetyData at sdLastVote
        lvr≡ : (pre ^∙ pssSafetyData-rm) ≡L safetyData at sdLastVotedRound
        vp≡pb : proposedBlock ≡ voteProposal ^∙ vpBlock

    contract'
      : ∀ pre pool
        → Requirements pre
        → LBFT-weakestPre
            (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock safetyData)
            (Contract pre pool proposedBlock) pre
    contract' pre pool reqs =
      verifyAndUpdateLastVoteRoundMSpec.contract (proposedBlock ^∙ bRound) safetyData
        (RWST-weakestPre-ebindPost unit step₁ (Contract pre pool proposedBlock)) pre
        contract-step₁
        (λ r≤lvr → contractBail _ refl)
      where
      module _ (r>lvr : proposedBlock ^∙ bRound > safetyData ^∙ sdLastVotedRound) where
        -- Shared definitions
        module _ where
          safetyData1 = verifyAndUpdateLastVoteRoundMSpec.safetyData' (proposedBlock ^∙ bRound) safetyData
          preUpdatedSD = pre & pssSafetyData-rm ∙~ safetyData1
          author = validatorSigner ^∙ vsAuthor

        -- State invariants
        module _ where
          qcP : Preserves (QCProps.SigsForVotes∈Rm-SentB4 pool) pre preUpdatedSD
          qcP qcsB4 = substSigsForVotes∈Rm-SentB4 refl qcsB4

          postulate -- TODO-1: prove (waiting on : `α-EC`)
            btip₁ : Preserves BlockStoreInv pre preUpdatedSD
         -- btip₁ = id

          emP : Preserves EpochsMatch pre preUpdatedSD
          emP eq = trans eq (Requirements.es≡₁ reqs)

          srP : Preserves SafetyRulesInv pre preUpdatedSD
          srP = mkPreservesSafetyRulesInv λ where (mkSafetyDataInv epoch≡ round≤) → mkSafetyDataInv (epoch≡P epoch≡) (round≤P round≤)
            where
            epoch≡P : Preserves (λ rm → Meta.getLastVoteEpoch rm ≡ rm ^∙ pssSafetyData-rm ∙ sdEpoch) pre preUpdatedSD
            epoch≡P epoch≡
              rewrite sym (Requirements.lv≡  reqs)
              |       sym (Requirements.es≡₁ reqs)
              = epoch≡

            round≤P : Preserves (λ rm → Meta.getLastVoteRound rm ≤ rm ^∙ pssSafetyData-rm ∙ sdLastVotedRound) pre preUpdatedSD
            round≤P round≤
               with pre ^∙ pssSafetyData-rm ∙ sdLastVote
               |    inspect (_^∙ pssSafetyData-rm ∙ sdLastVote) pre
            ...| nothing | [ lv≡ ] rewrite (trans (sym (Requirements.lv≡ reqs)) lv≡) = z≤n
            ...| just x  | [ lv≡ ] rewrite (trans (sym (Requirements.lv≡ reqs)) lv≡) =
              ≤-trans round≤ (≤-trans (≡⇒≤ (Requirements.lvr≡ reqs)) (<⇒≤ r>lvr))

          invP₁ : Preserves (RoundManagerInv pool) pre preUpdatedSD
          invP₁ = mkPreservesRoundManagerInv id qcP emP btip₁ srP

        -- Some lemmas
        module _ where
          lvr<pbr : pre ^∙ pssSafetyData-rm ∙ sdLastVotedRound < proposedBlock ^∙ bRound
          lvr<pbr rewrite (Requirements.lvr≡ reqs) = r>lvr

          vpr≡pbr : (voteProposal ^∙ vpBlock) ≡L proposedBlock at bRound
          vpr≡pbr rewrite Requirements.vp≡pb reqs = refl

        bailAfterSetSafetyData : ∀ e → Contract pre pool proposedBlock (Left e) preUpdatedSD []
        bailAfterSetSafetyData e =
          mkContract invP₁ refl refl false (mkVoteNotGenerated (Requirements.lv≡ reqs) lvr<pbr)

        contract-step₁ : RWST-weakestPre-ebindPost unit step₁ (Contract pre pool proposedBlock) (Right _) pre []
        contract-step₂ : RWST-weakestPre-ebindPost unit (step₂ safetyData1) (Contract pre pool proposedBlock) (Right _) preUpdatedSD []

        contract-step₁ ._ refl ._ refl .unit refl =
          extensionCheckSpec.contract voteProposal
            (λ r → RWST-weakestPre-ebindPost unit (step₂ safetyData1) (Contract pre pool proposedBlock) r preUpdatedSD [])
            bailAfterSetSafetyData contract-step₂

        contract-step₂ voteData@._ refl =
          constructLedgerInfoMSpec.contract proposedBlock (hashVD voteData)
            (RWST-weakestPre-∙^∙Post unit (withErrCtx ("" ∷ []))
              (RWST-weakestPre-ebindPost unit (step₃ safetyData1 voteData author) (Contract pre pool proposedBlock))) preUpdatedSD
              (λ where .(Left fakeErr) refl → bailAfterSetSafetyData fakeErr)
              contract-step₃
          where
          contract-step₃
            : ∀ ledgerInfo
              → RWST-weakestPre-∙^∙Post unit (withErrCtx ("" ∷ []))
                  (RWST-weakestPre-ebindPost unit (step₃ safetyData1 _ author) (Contract pre pool proposedBlock))
                  (Right ledgerInfo) preUpdatedSD []
          contract-step₃ ledgerInfo ._ refl ._ refl ._ refl .unit refl unit refl =
            mkContract invP₂ refl refl false
              (Voting.mkVoteGeneratedCorrect
                (mkVoteGenerated refl
                  (inj₂ (mkVoteNewGenerated lvr<pbr vpr≡pbr)))
              voteFromBlock)
            where
            vote = Vote.newWithSignature voteData author ledgerInfo (ValidatorSigner.sign validatorSigner ledgerInfo)
            preUpdatedSD₂ = preUpdatedSD & pssSafetyData-rm ∙~ (safetyData1 & sdLastVote ?~ vote)

            pb≡vpb = sym (Requirements.vp≡pb reqs)

            voteFromBlock : Voting.VoteMadeFromBlock vote proposedBlock
            voteFromBlock =
              Voting.mkVoteMadeFromBlock
                (cong (_^∙ bEpoch) pb≡vpb) (cong (_^∙ bRound) pb≡vpb) (cong (_^∙ bId) pb≡vpb)

            -- State invariants
            module _ where
              qcP₂ : Preserves (QCProps.SigsForVotes∈Rm-SentB4 pool) pre preUpdatedSD₂
              qcP₂ qcsB4 = substSigsForVotes∈Rm-SentB4 refl qcsB4

              postulate -- TODO-1: prove (waiting on: `α-EC`)
                btiP₂ : Preserves BlockStoreInv pre preUpdatedSD₂
             -- btiP₂ = id

              srP₂ : Preserves SafetyRulesInv pre preUpdatedSD₂
              srP₂ = mkPreservesSafetyRulesInv
                       (const $ mkSafetyDataInv (Requirements.es≡₂ reqs) (≡⇒≤ (cong (_^∙ bRound) pb≡vpb)))

              invP₂ : Preserves (RoundManagerInv pool) pre preUpdatedSD₂
              invP₂ = mkPreservesRoundManagerInv id qcP₂ emP btiP₂ srP₂

    contract
      : ∀ pre pool Post
        → Requirements pre
        → RWST-Post-⇒ (Contract pre pool proposedBlock) Post
        → LBFT-weakestPre
            (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock safetyData)
            Post pre
    contract pre pool Post reqs pf =
      LBFT-⇒ (Contract pre pool proposedBlock) Post pf (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock safetyData) pre
        (contract' pre pool reqs)

  module continue1
    (voteProposal  : VoteProposal) (validatorSigner : ValidatorSigner)
    (proposedBlock : Block)        (safetyData0     : SafetyData) where

    open constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0

    record Requirements (pre : RoundManager) : Set where
      constructor mkRequirements
      field
        sd≡   : pre ^∙ pssSafetyData-rm ≡ safetyData0
        es≡   : voteProposal ^∙ vpBlock ∙ bEpoch ≡ safetyData0 ^∙ sdEpoch
        vp≡pb : proposedBlock ≡ voteProposal ^∙ vpBlock

    contract
      : ∀ pre pool → Requirements pre
        → LBFT-weakestPre (constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0)
            (Contract pre pool proposedBlock) pre
    contract pre pool reqs =
      verifyQcMSpec.contract (proposedBlock ^∙ bQuorumCert)
        (RWST-weakestPre-ebindPost unit (λ _ → step₁) (Contract pre pool proposedBlock)) pre
        (contractBail _ refl)
        contract-step₁
      where
      contract-step₁ : QuorumCertProps.Contract _ _ → RWST-weakestPre-ebindPost unit (const step₁) (Contract pre pool proposedBlock) (Right unit) pre []
      contract-step₁ qcCon ._ refl validatorVerifier@._ refl
        with Block.validateSignature proposedBlock validatorVerifier
      ... | Left e = contractBail _ refl
      ... | Right unit = λ where ._ refl → contract-step₃
        where
        contract-step₃ : RWST-weakestPre step₃ (Contract pre pool proposedBlock) unit pre
        contract-step₃ =
          LBFT-⇒ (VAUPContract pre) Pred pf-step₃ (verifyAndUpdatePreferredRoundM (proposedBlock ^∙ bQuorumCert) safetyData0) pre
            (verifyAndUpdatePreferredRoundMSpec.contract (proposedBlock ^∙ bQuorumCert) safetyData0 pre) 
          -- verifyAndUpdatePreferredRoundMSpec.contract (proposedBlock ^∙ bQuorumCert) safetyData0
          --   Pred pre (λ r≤pr → contractBail _ refl) cases
            where
            VAUPContract = verifyAndUpdatePreferredRoundMSpec.Contract (proposedBlock ^∙ bQuorumCert) safetyData0
            Pred = RWST-weakestPre-ebindPost unit
                     (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock)
                     (Contract pre pool proposedBlock)

            reqs₁ : continue2.Requirements voteProposal validatorSigner proposedBlock safetyData0 pre
            reqs₁
              with Requirements.sd≡ reqs
            ...| refl = continue2.mkRequirements refl (Requirements.es≡ reqs) refl refl (Requirements.vp≡pb reqs)

            reqs₂ : continue2.Requirements voteProposal validatorSigner proposedBlock
                      (verifyAndUpdatePreferredRoundDefs.safetyData' (proposedBlock ^∙ bQuorumCert) safetyData0)
                      pre
            reqs₂
              with Requirements.sd≡ reqs
            ...| refl = continue2.mkRequirements refl (Requirements.es≡ reqs) refl refl (Requirements.vp≡pb reqs)

            pf-step₃ : ∀ r st outs → VAUPContract pre r st outs → Pred r st outs
            pf-step₃ r st outs (verifyAndUpdatePreferredRoundMSpec.mkContract noOuts refl condCorr) = pf r condCorr
              where
              pf-Con++outs : RWST-Post-⇒ (Contract pre pool proposedBlock) (RWST-Post++ (Contract pre pool proposedBlock) outs)
              pf-Con++outs r' st' outs' (mkContract rmInv noEpochChange noMsgOuts lvr≡? voteResCorrect) =
                mkContract rmInv noEpochChange (OutputProps.++-NoMsgs outs outs' noOuts noMsgOuts) lvr≡? voteResCorrect

              pf : (r : Either ErrLog SafetyData) (cc : verifyAndUpdatePreferredRoundMSpec.ConditionCorrect _ _ pre r) → Pred r st outs
              pf (Left e) tt = contractBail outs noOuts
              pf (Right .safetyData0) record { ep≡ = ep≡ ; qcr≤pr = qcr≤pr ; conds = (Left record { noUpd = refl }) } ._ refl =
                continue2.contract voteProposal validatorSigner proposedBlock safetyData0 pre pool
                  (RWST-Post++ (Contract pre pool proposedBlock) outs) reqs₁
                  pf-Con++outs
              pf (Right safetyData1@._) record { ep≡ = ep≡ ; qcr≤pr = qcr≤pr ; conds = (Right record { eff = refl }) } ._ refl =
                continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre pool
                  (RWST-Post++ (Contract pre pool proposedBlock) outs)
                  reqs₂ pf-Con++outs

  module continue0
    (voteProposal  : VoteProposal) (validatorSigner : ValidatorSigner) where

    open constructAndSignVoteM-continue0 voteProposal validatorSigner

    contract
      : ∀ pre pool
        → LBFT-weakestPre
            (constructAndSignVoteM-continue0 voteProposal validatorSigner) (Contract pre pool proposedBlock) pre
    contract pre pool safetyData0@._ refl =
      -- NOTE: There is a redundant check for this (that the proposal epoch
      -- matches the safety data epoch) in `LibraBFT.Impl.Consensus.Network`
      verifyEpochMSpec.contract (proposedBlock ^∙ bEpoch) safetyData0
        (RWST-weakestPre-ebindPost unit (const (step₁ safetyData0)) (Contract pre pool proposedBlock)) pre
        (λ e≢sde → contractBail _ refl)
        contract-step₁
      where
      module _ (e≡sde : proposedBlock ^∙ bEpoch ≡ pre ^∙ pssSafetyData-rm ∙ sdEpoch) where
        contract-step₁
          : RWST-weakestPre-ebindPost unit (const (step₁ safetyData0)) (Contract pre pool proposedBlock) (Right unit) pre []
        proj₁ (contract-step₁ .unit refl) ≡nothing =
          continue1.contract voteProposal validatorSigner proposedBlock safetyData0 pre pool
            (continue1.mkRequirements refl e≡sde refl)
        proj₁ (proj₂ (contract-step₁ .unit refl) vote vote≡) lvr≡pbr =
          mkContract reflPreservesRoundManagerInv (reflNoEpochChange{pre}) refl
            true (Voting.mkVoteGeneratedCorrect
                   (mkVoteGenerated (sym vote≡)
                     (inj₁ reflVoteOldGenerated))
                   (toWitnessT lvr≡pbr))
        proj₂ (proj₂ (contract-step₁ .unit refl) vote vote≡) lvr≢pbr =
          continue1.contract voteProposal validatorSigner proposedBlock safetyData0 pre pool
            (continue1.mkRequirements refl e≡sde refl)

  module _ (maybeSignedVoteProposal : MaybeSignedVoteProposal) where

    voteProposal  = maybeSignedVoteProposal ^∙ msvpVoteProposal
    proposedBlock = voteProposal ^∙ vpBlock

    contract'
      : ∀ pre
        → LBFT-weakestPre (constructAndSignVoteM maybeSignedVoteProposal) (Contract pre proposedBlock) pre
    contract' pre nothing vs≡ =
      mkContract
        reflPreservesRoundManagerInv (reflNoEpochChange{pre})
        refl true reflVoteNotGenerated
    contract' pre (just validatorSigner) vs≡ = continue0.contract voteProposal validatorSigner pre

    contract
      : ∀ pre pool Post → RWST-Post-⇒ (Contract pre pool proposedBlock) Post
        → LBFT-weakestPre (constructAndSignVoteM maybeSignedVoteProposal) Post pre
    contract pre pool Post pf =
      RWST-⇒ (Contract pre pool proposedBlock) Post pf (constructAndSignVoteM maybeSignedVoteProposal) unit pre
        (contract' pre pool)

private
  module Tutorial
    (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner)
    (proposedBlock : Block)       (safetyData : SafetyData) where

    -- After some experience with these proofs, it (allegedly)
    -- becomes fairly straightforward to let Agda do a lot of the
    -- work, and unfold the proof as we go.  However, it is
    -- important to understand what's going on under the hood to be
    -- able to reliably do this.  For the proof below, we do it in
    -- excruciating detail "by hand" in comments as an example to
    -- help ourselves understand.

    -- For this example, we will prove that `step₃` of (and old version of)
    -- `constructAndSignVoteM-continue2` produces no output.

    Contract : LBFT-Post (Either ErrLog Vote)
    Contract x post outs = outs ≡ []

    step₃ : SafetyData → VoteData → Author → LedgerInfo → LBFT (Either ErrLog Vote)
    step₃ safetyData1 voteData author ledgerInfo = do
      let signature = ValidatorSigner.sign validatorSigner ledgerInfo
          vote      = Vote.newWithSignature voteData author ledgerInfo signature
      pssSafetyData-rm ∙= (safetyData1 & sdLastVote ?~ vote)
      ok vote

    step₃-contract
      : ∀ pre safetyData1 voteData author ledgerInfo
        → LBFT-weakestPre
            (step₃ safetyData1 voteData author ledgerInfo)
            Contract pre
    step₃-contract pre safetyData1 voteData author ledgerInfo
    {-
    The proof can be as simple as this:

       = λ _ _ _ _ → refl

    Easy, right?!  Oh, you want a little more detail?  Sure here you go:

       = λ where .pre refl →
                  λ where .unit refl →
                           refl   -- Indenting important for parsing

    Still not crystal clear?  OK, let's explore in a little more detail.

    The initial goal looks like this:

    RWST-weakestPre-bindPost unit
      (λ st →
         RWST-put
         (LibraBFT.ImplShared.Consensus.Types.s st
          ((λ { F rf f (SafetyRules∙new v vv vvv)
                  → (rf Category.Functor.RawFunctor.<$>
                     (λ y' → SafetyRules∙new y' vv vvv))
                    (f v)
              })
           (λ x → x) Optics.Functorial.if
           ((λ { F rf f (PersistentSafetyStorage∙new v vv)
                   → (rf Category.Functor.RawFunctor.<$>
                      (λ y' → PersistentSafetyStorage∙new y' vv))
                     (f v)
               })
            (λ x → x) Optics.Functorial.if
            (λ _ →
               safetyData1 &
               sdLastVote ?~
               Vote.newWithSignature voteData author ledgerInfo
               (ValidatorSigner.sign validatorSigner ledgerInfo)))
           (LibraBFT.ImplShared.Consensus.Types.g st))))
      (RWST-weakestPre-bindPost unit
       (λ _ →
          RWST-return
          (inj₂
           (Vote.newWithSignature voteData author ledgerInfo
            (ValidatorSigner.sign validatorSigner ledgerInfo))))
       Contract)
      pre pre []

   It looks a bit ugly, but if we use C-u C-c C-, we get a more
   readable version that is exactly what we expect:

     LBFT-weakestPre (step₃ safetyData1 voteData author ledgerInfo)
                     Contract
                     pre

   Let's start refining by hand to understand.

   By desugaring the definition of "step₃ safetyData voteData author
   ledgerInfo" a bit, we can see that it is (using some shorthand in
   "quotes" to keep it concise at the expense of accuracy):

      (RWST-bind
         (RWST-bind
            (RWST-gets id)                                                                -- Fetch the state.
            (λ st → RWST-put (st & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote")))-- Modify the state returned by RWST-get.
         (λ _ → RWST-return (inj₂ "vote"))                                                -- The Unit returned by RWST-bind
                                                                                          -- via RWST-put is ignored

      Note that "vote" is: Vote.newWithSignature voteData author ledgerInfo
                             (ValidatorSigner.sign validatorSigner ledgerInfo)

   Rewriting our goal with this yields (the annotations on the right
   show how we instantiate the rules in the next step):

     RWST-weakestPre
      (RWST-bind
         (RWST-bind                                                              = m
            (RWST-gets id)
            (λ st → RWST-put (st & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote")))
         (λ _ → RWST-return (inj₂ "vote"))                                       = f
      Contract                                                                   = P
      unit                                                                       = ev
      pre                                                                        = st

   Applying the definition of RWST-weakestPre (RWST-bind...), we need:

     RWST-weakestPre
       (RWST-bind
            (RWST-gets id)                                                                 = m
            (λ st → RWST-put (st & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote"))) = f
       (RWST-weakestPre-bindPost unit                                                      = P
         (λ _ → RWST-return (inj₂ vote))
         Contract)
       unit                                                                                = ev
       pre                                                                                 = pre

   Applying the definition of RWST-weakestPre (RWST-bind...) again, we have:

     RWST-weakestPre
       (RWST-gets id)
       (RWST-weakestPre-bindPost unit                                            = P
         (λ st → RWST-put (st & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote")))
         (RWST-weakestPre-bindPost unit
           (λ _ → RWST-return (inj₂ vote))
           Contract))
       unit                                                                      = ev
       pre                                                                       = pre

   Now applying the definition of RWST-weakestPre RWST-gets, we want:

     (RWST-weakestPre-bindPost
         unit                                                                           = ev
         (λ st → RWST-put (st & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote"))) = f
         (RWST-weakestPre-bindPost unit                                                 = Post
           (λ _ → RWST-return (inj₂ "vote"))
           Contract))
       pre                                                                              = x
       pre                                                                              = post
       []                                                                               = outs

   Take a moment to compare this with our initial goal above.  They
   look identical, except for the shorthand.

   Next, we apply the definition of RWST-weakestPre-bindPost:

     ∀ r → r ≡ pre →
       RWST-weakestPre
         (RWST-put (r & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote")))
         (RWST-Post++
           (RWST-weakestPre-bindPost unit                                        = P
             (λ _ → RWST-return (inj₂ "vote"))
             Contract)
           [])                                                                   = outs
         unit
         pre

   Notice that our "f" (the put operation) is applied to the quantified variable
   "r". This is to reduce the size of the refined goal after substitution
   (instead of "pre", in general "r" could be equal to a much more complex expression).

   Applying the definition of RWST-Post++, we have:

     ∀ r → r ≡ pre →
       RWST-weakestPre
         (RWST-put (r & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote")))
         (λ x post outs₁ → (RWST-weakestPre-bindPost unit
                             (λ _ → RWST-return (inj₂ "vote"))
                             Contract) x post ([] ++ outs₁))
         unit
         pre

   Our proof begins by peeling of the two first parameters, the first
   of which must be pre, due to the second:

   -}

       = λ where .pre refl →

   {-

   At this point, our goal looks like (using C-u C-c C-,):

   RWST-weakestPre
      (RWST-put
       (over pssSafetyData-rm
        (λ _ →
           safetyData1 &
           sdLastVote ?~
           Vote.newWithSignature voteData author ledgerInfo
           (ValidatorSigner.sign validatorSigner ledgerInfo))
        pre))
      (λ x post outs₁ →
         RWST-weakestPre-bindPost unit
         (λ _ →
            RWST-return
            (inj₂
             (Vote.newWithSignature voteData author ledgerInfo
              (ValidatorSigner.sign validatorSigner ledgerInfo))))
         Contract x post ([] ++ outs₁))
      unit pre

   We can see that this is a more precise version of what we have above (without the shorthand),
   repeated here:

       RWST-weakestPre
         (RWST-put (pre & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote"))) = post
         (λ x post outs₁ → (RWST-weakestPre-bindPost unit                         = P
                             (λ _ → RWST-return (inj₂ "vote"))
                             Contract) x post ([] ++ outs₁))
         unit
         pre

   Next, we apply the definition of RWST-weakestPre (RWST-put ...)

      (λ x post outs₁ → (RWST-weakestPre-bindPost unit
                          (λ _ → RWST-return (inj₂ "vote"))
                          Contract) x post ([] ++ outs₁))
      unit
      (pre & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote"))
      []

    Instantiating,

      RWST-weakestPre-bindPost
       unit                                                                   = ev
       (λ _ → RWST-return (inj₂ "vote"))                                      = f
       Contract                                                               = Post
       unit                                                                   = x
       (pre & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote"))          = post
       ([] ++ []))                                                            = outs

    Applying the definition of RWST-weakestPre-bindPost once again, we have:

      ∀ r → r ≡ unit → RWST-weakestPre
                         (RWST-return (inj₂ "vote"))
                         (RWST-Post++
                           Contract                                           = P
                           ([] ++ [])))                                       = outs
                         unit
                         (pre & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote"))

    And applying the definition of RWST-Post++ yields:

      ∀ r → r ≡ unit → RWST-weakestPre
                         (RWST-return (inj₂ "vote"))
                         (λ x post outs₁ → Contract rm x post ([] ++ [] ++ outs₁))
                         unit
                         (pre & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote"))

    Peeling off another couple of parameters (the first must be unit because of the second):
 -}

                      λ where .unit refl →


 {-

 The goal now looks like (using C-c C-,):

    Contract
      (inj₂
       (Vote.newWithSignature voteData author ledgerInfo
        (ValidatorSigner.sign validatorSigner ledgerInfo)))
      (LibraBFT.ImplShared.Consensus.Types.s pre
       ((λ { F rf f (SafetyRules∙new v vv vvv)
               → (rf Category.Functor.RawFunctor.<$>
                  (λ y' → SafetyRules∙new y' vv vvv))
                 (f v)
           })
        (λ x → x) Optics.Functorial.if
        ((λ { F rf f (PersistentSafetyStorage∙new v vv)
                → (rf Category.Functor.RawFunctor.<$>
                   (λ y' → PersistentSafetyStorage∙new y' vv))
                  (f v)
            })
         (λ x → x) Optics.Functorial.if
         (λ _ →
            safetyData1 &
            sdLastVote ?~
            Vote.newWithSignature voteData author ledgerInfo
            (ValidatorSigner.sign validatorSigner ledgerInfo)))
        (LibraBFT.ImplShared.Consensus.Types.g pre)))
      []

 Applying our shorthand, this yields:

    Contract
      (inj₂ "vote")
      (pre & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote"))
      []

 Or (using C-u C-c C-,), we have the following goal:

    RWST-weakestPre
      (RWST-return
       (inj₂
        (Vote.newWithSignature voteData author ledgerInfo
         (ValidatorSigner.sign validatorSigner ledgerInfo))))
      (λ x post outs₁ → Contract x post (([] ++ []) ++ outs₁)) unit
      (over pssSafetyData-rm
       (λ _ →
          safetyData1 &
          sdLastVote ?~
          Vote.newWithSignature voteData author ledgerInfo
          (ValidatorSigner.sign validatorSigner ledgerInfo))
       pre)

 Applying our shorthand, this yields:

     RWST-weakestPre
       (RWST-return (inj₂ "vote"))                                       = x
       (λ x post outs₁ → Contract x post ([] ++ [] ++ outs₁))            = P
       unit                                                              = ev
       (pre & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote"))     = pre

   Again, this looks like what we expect from above, so we can press
   on.  Now, applying the definition of RWST-weakestPre (RWST-return ...):

     (λ x post outs₁ → Contract x post ([] ++ [] ++ outs₁))
        (RWST-return (inj₂ "vote"))
        (pre & pssSafetyData-rm ∙~ ("safetyData1" & sdLastVote ?~ "vote"))
        []

   Finally, this reduces to the goal of:

     [] ≡ []

   which we prove with
   -}
                               refl
