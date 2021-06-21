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
    constructor mkContract
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

    open constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock safetyData

    -- After some experience with these proofs, it (allegedly)
    -- becomes fairly straightforward to let Agda do a lot of the
    -- work, and unfold the proof as we go.  However, it is
    -- important to understand what's going on under the hood to be
    -- able to reliably do this.  For the proof below, we do it in
    -- excruciating detail "by hand" in comments as an example to
    -- help ourselves understand.

    step₃-contract
        : ∀ rm pre safetyData voteData ledgerInfo →
          (RWST-weakestPre (step₃ safetyData voteData author ledgerInfo)
                           (Contract rm))
                           unit pre
    step₃-contract rm pre safetyData voteData ledgerInfo

    {-
    The proof can be as simple as this:

       = λ _ _ _ _ → mkContract refl refl

    Easy, right?!  Oh, you want a little more detail?  Sure here you go:

       = λ where .pre refl →
                  λ where .unit refl →
                           mkContract refl refl     -- Indenting important for parsing

    Still not crystal clear?  OK, let's explore in a little more detail.

    The initial goal looks like this (we explore why in detail below):

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
               safetyData &
               sdLastVote ?~
               Vote.newWithSignature voteData author ledgerInfo
               (ValidatorSigner.sign validatorSigner ledgerInfo)))
           (LibraBFT.ImplShared.Consensus.Types.g st))))
      (RWST-weakestPre-bindPost unit
       (λ _ →
          RWST-return
          (inj₂
           (VoteWithMeta∙new
            (Vote.newWithSignature voteData author ledgerInfo
             (ValidatorSigner.sign validatorSigner ledgerInfo))
            mvsNew)))
       (Contract rm))
      pre pre []

   It looks a bit ugly, but if we use C-u C-c C-, we get a more
   readable version that is exactly what we expect:

     RWST-weakestPre (step₃ safetyData voteData author ledgerInfo)
                     (Contract rm)
                     unit pre

   Let's start refining by hand to understand.

   By desugaring the definition of "step₃ safetyData voteData author
   ledgerInfo" a bit, we can see that it is (using some shorthand in
   "quotes" to keep it concise at the expense of accuracy):

      (RWST-bind
         (RWST-bind
            RWST-get
            (RWST-put "lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)"))   -- modifies the state returned by
                                                                              -- RWST-get
         (λ _ → RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))            -- The Unit returned by RWST-bind
                                                                              -- via RWST-put is ignored

   Rewriting our goal with this yields (the annotations on the right
   show how we instantiate the rules in the next step):

     RWST-weakestPre
      (RWST-bind
         (RWST-bind                                                              = m
            RWST-get
            (RWST-put "lSafetyData ∙= (safetyData1 [ sdLastVote ?= vote ])"))
         (λ _ → RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))               = f
      (Contract rm)                                                              = P
      unit                                                                       = ev
      pre                                                                        = st

   Applying the definition of RWST-weakestPre (RWST-bind...), we need:

     RWST-weakestPre
       (RWST-bind
            RWST-get                                                             = m
            (RWST-put "lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)"))      = f
       (RWST-weakestPre-bindPost unit                                            = P
         (λ _ → RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))
         (Contract rm))
       unit                                                                      = ev
       pre                                                                       = pre

   Applying the definition of RWST-weakestPre (RWST-bind...) again, we have:

     RWST-weakestPre
       RWST-get
       (RWST-weakestPre-bindPost unit                                            = P
         (RWST-put "lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)")
         (RWST-weakestPre-bindPost unit
           (λ _ → RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))
           (Contract rm)))
       unit                                                                      = ev
       pre                                                                       = pre

   Now applying the definition of RWST-weakestPre RWST-get, we want:

     (RWST-weakestPre-bindPost
         unit                                                                    = ev
         (RWST-put "lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)")          = f
         (RWST-weakestPre-bindPost unit                                          = Post
           (λ _ → RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))
           (Contract rm)))
       pre                                                                       = x
       pre                                                                       = post
       []                                                                        = outs

   Take a moment to compare this with our initial goal above.  They
   look identical, except for the shorthand.

   Next, we apply the definition of RWST-weakestPre-bindPost:

     ∀ r → r ≡ pre →
       RWST-weakestPre
         (RWST-put "lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)" pre)
         (RWST-Post++
           (RWST-weakestPre-bindPost unit                                        = P
             (λ _ → RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))
             (Contract rm))
           [])                                                                   = outs
         unit
         pre

   Applying the definition of RWST-Post++, we have:

     ∀ r → r ≡ pre →
       RWST-weakestPre
         (RWST-put "lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)" pre)
         (λ x post outs₁ → (RWST-weakestPre-bindPost unit
                             (λ _ → RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))
                             (Contract rm)) x post ([] ++ outs₁))
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
           safetyData &
           sdLastVote ?~
           Vote.newWithSignature voteData author ledgerInfo
           (ValidatorSigner.sign validatorSigner ledgerInfo))
        pre))
      (λ x post outs₁ →
         RWST-weakestPre-bindPost unit
         (λ _ →
            RWST-return
            (inj₂
             (VoteWithMeta∙new
              (Vote.newWithSignature voteData author ledgerInfo
               (ValidatorSigner.sign validatorSigner ledgerInfo))
              mvsNew)))
         (Contract rm) x post ([] ++ outs₁))
      unit pre

   We can see that this is a more precise version of what we have above (without the shorthand),
   repeated here:

       RWST-weakestPre
         (RWST-put "lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)" pre)   = post
         (λ x post outs₁ → (RWST-weakestPre-bindPost unit                     = P
                             (λ _ → RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))
                             (Contract rm)) x post ([] ++ outs₁))
         unit
         pre

   Next, we apply the defintion of RWST-weakestPre (RWST-put ...)

      (λ x post outs₁ → (RWST-weakestPre-bindPost unit
                          (λ _ → RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))
                          (Contract rm)) x post ([] ++ outs₁))
      unit
      ("lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)" pre)
      []

    Instantiating,

      RWST-weakestPre-bindPost
       unit                                                                   = ev
       (λ _ → RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))              = f
       (Contract rm)                                                          = Post
       unit                                                                   = x
       ("lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)" pre)              = post
       ([] ++ []))                                                            = outs

    Applying the definition of RWST-weakestPre-bindPost once again, we have:

      ∀ r → r ≡ unit → RWST-weakestPre
                         (RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))
                         (RWST-Post++
                           (Contract rm)                                      = P
                           ([] ++ [])))                                       = outs
                         unit
                         ("lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)" pre)

    And applying the definition of RWST-Post++ yields:

      ∀ r → r ≡ unit → RWST-weakestPre
                         (RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))
                         (λ x post outs₁ → VotesCorrect rm x post ([] ++ [] ++ outs₁))
                         unit
                         ("lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)" pre)

    Peeling off another couple of parameters (the first must be unit because of the second):
   -}

                      λ where .unit refl →


  {-

  The goal now looks like (using C-u C-c C-,):

    RWST-weakestPre
        (RWST-return
         (inj₂
          (VoteWithMeta∙new
           (Vote.newWithSignature voteData author ledgerInfo
            (ValidatorSigner.sign validatorSigner ledgerInfo))
           mvsNew)))
        (λ x post outs₁ → Contract rm x post (([] ++ []) ++ outs₁))
        unit
        (over lSafetyData
         (λ _ →
            set? sdLastVote
            (Vote.newWithSignature voteData author ledgerInfo
             (ValidatorSigner.sign validatorSigner ledgerInfo))
            safetyData)
         pre)

   Again, this looks like what we expect from above, so we can press
   on.  Returning to our shorthand version:

     RWST-weakestPre
       (RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))               = x
       (λ x post outs₁ → Contract rm x post ([] ++ [] ++ outs₁))         = P
       unit                                                              = ev
       ("lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)" pre)         = pre

   Now applying the definition of RWST-weakestPre (RWST-return ...):

     (λ x post outs₁ → Contract rm x post ([] ++ [] ++ outs₁))
        (RWST-return (inj₂ "VoteWithMeta∙new vote mvsNew"))
        ("lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)" pre)
        []

   To prove this, we need to provide two proofs to mkContract, the first of which (for noOutput).
   is simply [] ++ [] ++ [] ≡ [], which is easily dispatched with refl.

   The other is

     VoteSrcCorrect
       rm                                                                = pre
       (inj₂ "VoteWithMeta∙new vote mvsNew")                             = inj₂ mv
       ("lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)" pre)         = post
       ([] ++ [] ++ []))                                                 = outs

   By definition of VoteSrcCorrect, we have:

        VoteSrcCorrectCod
          rm                                                             = pre
          ("lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote)" pre)      = post
          ("VoteWithMeta∙new vote mvsNew")

   By definition of VoteSrcCorrectCod, this is:

        just vote ≡ ("lSafetyData ∙= (safetyData1 & sdLastVote ?~ vote) rm") ^∙ lSafetyData ∙ sdLastVote

        Which easily holds by definition of ?~, regardless of rm.

   Thus, the proof now really is simple:

   -}

                               mkContract refl refl


    step₂-contract
        : ∀ rm pre safetyData voteData →
          RWST-weakestPre (step₂ safetyData voteData) (Contract rm) unit pre
    step₂-contract rm pre safetyData voteData =
      ConstructLedgerInfoM.contract proposedBlock (Crypto.hashVD voteData)
                                    (RWST-weakestPre-ebindPost unit (step₃ safetyData voteData author) (Contract rm))
                                    pre  -- step₃ does not update state, so we can use pre???
                                    (mkContract refl unit)
                                    (λ ledgerInfo c →
                                       λ where refl → step₃-contract rm pre safetyData voteData ledgerInfo)

    step₁-contract
        : ∀ rm pre safetyData →
          RWST-weakestPre (step₁ safetyData) (Contract rm) unit pre
    step₁-contract rm pre safetyData1 = λ where
        .pre refl →     -- from RWST-weakestPre-bindPost, r , r ≡ x
          λ where
            _ refl →  -- Parameters of RWST-weakestPre-bindPost again, for ...
              let st₁ = pre & lSafetyData ∙~ safetyData1 in
                ExtensionCheckM.contract voteProposal
                                         (RWST-weakestPre-ebindPost unit (step₂ safetyData1) (Contract rm))
                                         st₁
                                         (mkContract refl unit)
                                         (λ voteData c →
                                           λ where refl → step₂-contract rm st₁ safetyData1 voteData)
    contract
      : ∀ rm pre
        → RWST-weakestPre
            (constructAndSignVoteM-continue2.step₀ voteProposal validatorSigner proposedBlock safetyData)
            (Contract rm) unit pre
    contract rm pre =
      VerifyAndUpdateLastVoteRoundM.contract round safetyData
        -- P
        (RWST-weakestPre-ebindPost unit step₁ (Contract rm))
        pre
        -- False case, VoteSrcCorrect holds trivially for inj₁ case
        (λ _ → mkContract refl unit)
        -- True case, ... now we get into it.
        -- C₁ true  c           c ≡ r
        (λ _rnd>lvr safetyData1 refl → step₁-contract rm pre safetyData1)

        {- Original unrolled proof, which is decomposed into smaller
           pieces above for pedagogical reasons:

        (λ _rnd>lvr safetyData1 _ →
          λ where
          ._ refl unit _ →
            let st₁ = pre & lSafetyData ∙~ safetyData1 in
            ExtensionCheckM.contract voteProposal (RWST-weakestPre-ebindPost unit (step₂ safetyData1) _) st₁
              (mkContract refl unit)
              λ _ voteData _ →
                ConstructLedgerInfoM.contract proposedBlock (Crypto.hashVD voteData)
                  (RWST-weakestPre-ebindPost _ (step₃ safetyData1 voteData author) _) st₁
                  (mkContract refl unit)
                  λ _ ledgerInfo _ → λ _ _ _ _ → mkContract refl refl)

        -}

  module Continue1
    (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner) (proposedBlock : Block)
    (safetyData0 : SafetyData)
    where

    c₃ : Unit → LBFT (ErrLog ⊎ VoteWithMeta)
    c₃ _ =
      verifyAndUpdatePreferredRoundM (proposedBlock ^∙ bQuorumCert) safetyData0 ∙?∙
        constructAndSignVoteM-continue2.step₀ voteProposal validatorSigner proposedBlock

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
        (mkContract refl unit)
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
                         Continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre pre)
                      , (λ twoChainRound<preferredRound safetyData1 safetyData1≡ →
                           Continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre pre)
                      , λ twoChainRound=preferredRound safetyData1 safetyData1≡ →
                          Continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre pre)
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
    proj₁ (contract pre vs vs≡) vs≡nothing = mkContract refl unit
    proj₂ (contract pre vs vs≡) j j≡ = Continue0.contract voteProposal j pre

    contract⇒ : ∀ pre Post
                → (∀ r st outs → Contract pre r st outs → Post r st outs)
                → RWST-weakestPre (constructAndSignVoteM maybeSignedVoteProposal) Post unit pre
    contract⇒ pre Post impl =
      RWST-impl (Contract pre) Post impl
        (constructAndSignVoteM maybeSignedVoteProposal) unit pre
        (contract pre)
