{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Optics.All
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
import      LibraBFT.ImplShared.Util.Crypto                         as Crypto
open import LibraBFT.ImplShared.Util.Util
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteData   as VoteData
open import LibraBFT.Impl.Consensus.RoundManager.PropertyDefs
open import LibraBFT.Impl.Consensus.SafetyRules.SafetyRules
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Types.ValidatorSigner               as ValidatorSigner
open import LibraBFT.Lemmas
open import LibraBFT.Prelude

module LibraBFT.Impl.Consensus.SafetyRules.Properties.SafetyRules where

module verifyAndUpdatePreferredRoundMSpec (quorumCert : QuorumCert) (safetyData : SafetyData) where
  preferredRound = safetyData ^∙ sdPreferredRound
  oneChainRound  = quorumCert ^∙ qcCertifiedBlock ∙ biRound
  twoChainRound  = quorumCert ^∙ qcParentBlock ∙ biRound

  C₁ = oneChainRound < preferredRound
  C₂ = twoChainRound > preferredRound
  C₃ = twoChainRound < preferredRound
  C₄ = twoChainRound ≡ preferredRound

  safetyData' = safetyData & sdPreferredRound ∙~ twoChainRound

  -- Before proving this, we should consider whether to add explicit support for <-cmp to our RWST
  -- support, to make this proof unroll more "automatically".

  postulate
    contract
      : ∀ P pre
        → ((1cr<pr : C₁) → P (inj₁ fakeErr) pre [])
        → ((1cr≥pr : ¬ C₁)
           → ((2cr>pr : C₂) → P (inj₂ safetyData') pre [])
              × ((2cr<pr : C₃) → P (inj₂ safetyData) pre [])
              × ((2cr=pr : C₄) → P (inj₂ safetyData) pre []))
        → LBFT-weakestPre (verifyAndUpdatePreferredRoundM quorumCert safetyData) P pre

module extensionCheckMSpec (voteProposal : VoteProposal) where
  proposedBlock = voteProposal ^∙ vpBlock
  voteData = VoteData.new (Block.genBlockInfo proposedBlock) (proposedBlock ^∙ bQuorumCert ∙ qcCertifiedBlock)

  -- TODO-1: This contract requires refinement once `extensionCheckM` is fully
  -- implemented.
  contract
    : ∀ P pre
      → P (inj₁ fakeErr) pre []
      → P (inj₂ voteData) pre []
      → LBFT-weakestPre (extensionCheckM voteProposal) P pre
  contract Post pre prfBail prfOk = prfOk

module constructLedgerInfoMSpec (proposedBlock : Block) (consensusDataHash : HashValue) where
  -- TODO-1: This is a place-holder contract that requires refinement once
  -- `constructLedgerInfoM is implemented.
  postulate
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


module verifyQcMSpec (qc : QuorumCert) where
  postulate
    -- TODO-1: This contract needs refinement.
    contract
      : ∀ P pre
        → (P (inj₁ fakeErr) pre [])
        → (P (inj₂ unit) pre [])
        → LBFT-weakestPre (verifyQcM qc) P pre

module constructAndSignVoteMSpec where

  ResultCorrect : (pre post : RoundManager) (strict : Bool) (epoch : Epoch) (round : Round) (r : Either ErrLog Vote) → Set
  ResultCorrect pre post strict epoch round (Left e) = NoVoteCorrect pre post strict
  ResultCorrect pre post strict epoch round (Right v) = VoteCorrect pre post epoch round v

  record Contract (pre : RoundManager) (epoch : Epoch) (round : Round) (r : Either ErrLog Vote) (post : RoundManager) (outs : List Output) : Set where
    constructor mkContract
    field
      noOuts        : NoMsgOuts outs
      inv           : NoEpochChange pre post
      lvr≡?    : Bool
      resultCorrect : ResultCorrect pre post lvr≡? epoch round r

  private
    contractBail : ∀ {pre e epoch round} → Contract pre epoch round (Left e) pre []
    contractBail = mkContract refl reflNoEpochChange true reflNoVoteCorrect

  module continue2
    (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner)
    (proposedBlock : Block) (safetyData : SafetyData) where

    open constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock safetyData

    record Requirements (pre : RoundManager) : Set where
      constructor mkRequirements
      field
        es≡  : (pre ^∙ lSafetyData) ≡L safetyData at sdEpoch
        lv≡  : (pre ^∙ lSafetyData) ≡L safetyData at sdLastVote
        lvr≡ : (pre ^∙ lSafetyData) ≡L safetyData at sdLastVotedRound
        vp≡pb : proposedBlock ≡ voteProposal ^∙ vpBlock

    epoch = voteProposal ^∙ vpBlock ∙ bEpoch
    round = voteProposal ^∙ vpBlock ∙ bRound

    contract
      : ∀ pre
        → Requirements pre
        → LBFT-weakestPre
            (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock safetyData)
            (Contract pre epoch round) pre
    contract pre reqs =
      verifyAndUpdateLastVoteRoundMSpec.contract (proposedBlock ^∙ bRound) safetyData
        (RWST-weakestPre-ebindPost unit step₁ (Contract pre epoch round)) pre
        contract-step₁
        (λ r≤lvr → contractBail)
      where
      module _ (r>lvr : proposedBlock ^∙ bRound > safetyData ^∙ sdLastVotedRound) where
        safetyData1 = verifyAndUpdateLastVoteRoundMSpec.safetyData' (proposedBlock ^∙ bRound) safetyData
        preUpdatedSD = pre & lSafetyData ∙~ safetyData1
        author = validatorSigner ^∙ vsAuthor

        lvr<pbr : pre ^∙ lSafetyData ∙ sdLastVotedRound < proposedBlock ^∙ bRound
        lvr<pbr rewrite (Requirements.lvr≡ reqs) = r>lvr

        vpr≡pbr : (voteProposal ^∙ vpBlock) ≡L proposedBlock at bRound
        vpr≡pbr rewrite Requirements.vp≡pb reqs = refl

        bailAfterSetSafetyData : Contract pre epoch round (Left fakeErr) preUpdatedSD []
        bailAfterSetSafetyData =
          mkContract refl (mkNoEpochChange refl (Requirements.es≡ reqs))
            false (mkNoVoteCorrect (Requirements.lv≡ reqs) lvr<pbr)

        contract-step₁ : RWST-weakestPre-ebindPost unit step₁ (Contract pre epoch round) (Right _) pre []
        contract-step₂ : RWST-weakestPre-ebindPost unit (step₂ safetyData1) (Contract pre epoch round) (Right _) preUpdatedSD []
        contract-step₃
          : ∀ ledgerInfo
            → RWST-weakestPre-∙^∙Post unit withErrCtxt
                (RWST-weakestPre-ebindPost unit (step₃ safetyData1 _ author) (Contract pre epoch round))
                (Right ledgerInfo) preUpdatedSD []

        contract-step₁ ._ refl ._ refl .unit refl =
          extensionCheckMSpec.contract voteProposal
            (RWST-weakestPre-ebindPost unit (step₂ safetyData1) (Contract pre epoch round)) preUpdatedSD
            bailAfterSetSafetyData
            contract-step₂

        contract-step₂ voteData@._ refl =
          constructLedgerInfoMSpec.contract proposedBlock (hashVD voteData)
            (RWST-weakestPre-∙^∙Post unit withErrCtxt
              (RWST-weakestPre-ebindPost unit (step₃ safetyData1 voteData author) (Contract pre epoch round))) preUpdatedSD
              (λ where .(Left fakeErr) refl → bailAfterSetSafetyData)
              contract-step₃

        contract-step₃ ledgerInfo ._ refl ._ refl ._ refl .unit refl unit refl =
          mkContract refl (mkNoEpochChange refl (Requirements.es≡ reqs))
            false
            (mkVoteCorrect
              (mkVoteCorrectInv refl refl)
              (Right (mkVoteCorrectNew refl lvr<pbr vpr≡pbr)))

  module continue1
    (voteProposal  : VoteProposal) (validatorSigner : ValidatorSigner)
    (proposedBlock : Block)        (safetyData0     : SafetyData) where

    open constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0

    epoch = voteProposal ^∙ vpBlock ∙ bEpoch
    round = voteProposal ^∙ vpBlock ∙ bRound

    record Requirements (pre : RoundManager) : Set where
      constructor mkRequirements
      field
        sd≡   : pre ^∙ lSafetyData ≡ safetyData0
        vp≡pb : proposedBlock ≡ voteProposal ^∙ vpBlock

    -- TODO-1: Break this down into smaller pieces.
    contract
      : ∀ pre
        → Requirements pre
        → LBFT-weakestPre
            (constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0)
            (Contract pre epoch round) pre
    contract pre reqs =
      verifyQcMSpec.contract (proposedBlock ^∙ bQuorumCert)
        (RWST-weakestPre-ebindPost unit (λ _ → step₁) (Contract pre epoch round)) pre
          contractBail
          λ where
            ._ refl validatorVerifier@._ refl →
              either{C = λ x → RWST-weakestPre (pure x ∙?∙ λ _ → step₃) (Contract pre epoch round) _ _}
                (λ _ → contractBail)
                (λ where
                  unit .unit refl →
                    verifyAndUpdatePreferredRoundMSpec.contract (proposedBlock ^∙ bQuorumCert) safetyData0
                      (RWST-weakestPre-ebindPost unit
                        (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock)
                        (Contract pre epoch round))
                      pre
                      (λ r≤pr → contractBail)
                      λ r>pr →
                        (  λ where
                            2cr>pr safetyData1@._ refl →
                              continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre
                                reqs₂)
                        , (λ where
                             2cr<pr safetyData1@._ refl →
                               continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre
                                 reqs₁)
                        , λ where
                            2cr=pr safetyData1@._ refl →
                              continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre
                                reqs₁)
                (Block.validateSignature proposedBlock validatorVerifier)
      where
      reqs₁ : continue2.Requirements voteProposal validatorSigner proposedBlock safetyData0 pre
      reqs₁
         with Requirements.sd≡ reqs
      ...| refl = continue2.mkRequirements refl refl refl (Requirements.vp≡pb reqs)

      reqs₂ : continue2.Requirements voteProposal validatorSigner proposedBlock
                (verifyAndUpdatePreferredRoundMSpec.safetyData' (proposedBlock ^∙ bQuorumCert) safetyData0)
                pre
      reqs₂
         with Requirements.sd≡ reqs
      ...| refl = continue2.mkRequirements refl refl refl (Requirements.vp≡pb reqs)

  module continue0
    (voteProposal  : VoteProposal) (validatorSigner : ValidatorSigner) where

    open constructAndSignVoteM-continue0 voteProposal validatorSigner

    epoch = voteProposal ^∙ vpBlock ∙ bEpoch
    round = voteProposal ^∙ vpBlock ∙ bRound

    contract
      : ∀ pre
        → LBFT-weakestPre
            (constructAndSignVoteM-continue0 voteProposal validatorSigner) (Contract pre epoch round) pre
    contract pre safetyData0@._ refl =
      -- NOTE: There is a redundant check for this (that the proposal epoch
      -- matches the safety data epoch) in `LibraBFT.Impl.Consensus.Network`
      verifyEpochMSpec.contract (proposedBlock ^∙ bEpoch) safetyData0
        (RWST-weakestPre-ebindPost unit (const (step₁ safetyData0)) (Contract pre epoch round)) pre
        (λ e≢sde → contractBail)
        λ e≡sde → contract-step₁
      where
      contract-step₁
        : RWST-weakestPre-ebindPost unit (const (step₁ safetyData0)) (Contract pre epoch round) (Right unit) pre []
      proj₁ (contract-step₁ .unit refl) ≡nothing =
        continue1.contract voteProposal validatorSigner proposedBlock safetyData0 pre
          (continue1.mkRequirements refl refl)
      proj₁ (proj₂ (contract-step₁ .unit refl) vote vote≡) lvr≡pbr =
        mkContract refl reflNoEpochChange true
          (mkVoteCorrect (mkVoteCorrectInv (toWitnessT lvr≡pbr) (sym vote≡))
            (Left reflVoteCorrectOld))
      proj₂ (proj₂ (contract-step₁ .unit refl) vote vote≡) lvr≢pbr =
        continue1.contract voteProposal validatorSigner proposedBlock safetyData0 pre
          (continue1.mkRequirements refl refl)

  module _ (maybeSignedVoteProposal : MaybeSignedVoteProposal) where

    voteProposal = maybeSignedVoteProposal ^∙ msvpVoteProposal
    epoch = voteProposal ^∙ vpBlock ∙ bEpoch
    round = voteProposal ^∙ vpBlock ∙ bRound

    contract'
      : ∀ pre
        → LBFT-weakestPre (constructAndSignVoteM maybeSignedVoteProposal) (Contract pre epoch round) pre
    contract' pre .unit refl nothing vs≡ ._ refl .unit refl =
      mkContract refl reflNoEpochChange true reflNoVoteCorrect
    contract' pre .unit refl (just validatorSigner) vs≡ =
      RWST-⇒
        (Contract pre epoch round) Post pf
        (constructAndSignVoteM-continue0 voteProposal validatorSigner) unit pre
        (continue0.contract voteProposal validatorSigner pre)
      where
      Post : LBFT-Post (Either ErrLog Vote)
      Post x post outs =
        RWST-weakestPre-bindPost unit
          (λ r → logInfo >> pure r) (Contract pre epoch round)
          x post (LogInfo fakeInfo ∷ outs)

      pf : ∀ r st outs → Contract pre epoch round r st outs → Post r st outs
      pf r st outs (mkContract noOuts inv lvr≡? resultCorrect) ._ refl .unit refl =
        mkContract (++-NoMsgOuts outs (LogInfo fakeInfo ∷ []) noOuts refl) inv lvr≡? resultCorrect

    contract
      : ∀ pre Post → (∀ r st outs → Contract pre epoch round r st outs → Post r st outs)
        → LBFT-weakestPre (constructAndSignVoteM maybeSignedVoteProposal) Post pre
    contract pre Post pf =
      RWST-⇒ (Contract pre epoch round) Post pf (constructAndSignVoteM maybeSignedVoteProposal) unit pre
        (contract' pre)

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
      lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)
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
            (λ st → RWST-put (st & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote")))-- Modify the state returned by RWST-get.
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
            (λ st → RWST-put (st & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote")))
         (λ _ → RWST-return (inj₂ "vote"))                                       = f
      Contract                                                                   = P
      unit                                                                       = ev
      pre                                                                        = st

   Applying the definition of RWST-weakestPre (RWST-bind...), we need:

     RWST-weakestPre
       (RWST-bind
            (RWST-gets id)                                                                 = m
            (λ st → RWST-put (st & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))) = f
       (RWST-weakestPre-bindPost unit                                                      = P
         (λ _ → RWST-return (inj₂ vote))
         Contract)
       unit                                                                                = ev
       pre                                                                                 = pre

   Applying the definition of RWST-weakestPre (RWST-bind...) again, we have:

     RWST-weakestPre
       (RWST-gets id)
       (RWST-weakestPre-bindPost unit                                            = P
         (λ st → RWST-put (st & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote")))
         (RWST-weakestPre-bindPost unit
           (λ _ → RWST-return (inj₂ vote))
           Contract))
       unit                                                                      = ev
       pre                                                                       = pre

   Now applying the definition of RWST-weakestPre RWST-gets, we want:

     (RWST-weakestPre-bindPost
         unit                                                                           = ev
         (λ st → RWST-put (st & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))) = f
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
         (RWST-put (r & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote")))
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
         (RWST-put (r & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote")))
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
       (over lSafetyData
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
         (RWST-put (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))) = post
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
      (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))
      []

    Instantiating,

      RWST-weakestPre-bindPost
       unit                                                                   = ev
       (λ _ → RWST-return (inj₂ "vote"))                                      = f
       Contract                                                               = Post
       unit                                                                   = x
       (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))          = post
       ([] ++ []))                                                            = outs

    Applying the definition of RWST-weakestPre-bindPost once again, we have:

      ∀ r → r ≡ unit → RWST-weakestPre
                         (RWST-return (inj₂ "vote"))
                         (RWST-Post++
                           Contract                                           = P
                           ([] ++ [])))                                       = outs
                         unit
                         (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))

    And applying the definition of RWST-Post++ yields:

      ∀ r → r ≡ unit → RWST-weakestPre
                         (RWST-return (inj₂ "vote"))
                         (λ x post outs₁ → Contract rm x post ([] ++ [] ++ outs₁))
                         unit
                         (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))

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
      (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))
      []

 Or (using C-u C-c C-,), we have the following goal:

    RWST-weakestPre
      (RWST-return
       (inj₂
        (Vote.newWithSignature voteData author ledgerInfo
         (ValidatorSigner.sign validatorSigner ledgerInfo))))
      (λ x post outs₁ → Contract x post (([] ++ []) ++ outs₁)) unit
      (over lSafetyData
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
       (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))     = pre

   Again, this looks like what we expect from above, so we can press
   on.  Now, applying the definition of RWST-weakestPre (RWST-return ...):

     (λ x post outs₁ → Contract x post ([] ++ [] ++ outs₁))
        (RWST-return (inj₂ "vote"))
        (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))
        []

   Finally, this reduces to the goal of:

     [] ≡ []

   which we prove with
   -}
                               refl
