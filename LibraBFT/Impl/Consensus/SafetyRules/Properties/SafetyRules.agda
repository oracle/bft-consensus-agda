{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.KVMap                               as Map
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
import      LibraBFT.ImplShared.Util.Crypto                   as Crypto
open import LibraBFT.ImplShared.Util.Util
import      LibraBFT.Impl.Types.LedgerInfoWithSignatures      as LedgerInfoWithSignatures
open import LibraBFT.Impl.Types.ValidatorSigner               as ValidatorSigner
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.Properties.QuorumCert as QuorumCertProps
import      LibraBFT.Impl.Consensus.ConsensusTypes.Properties.VoteData as VotaDataProps
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteData   as VoteData
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

  -- Before proving this, we should consider whether to add explicit support for <-cmp to our RWST
  -- support, to make this proof unroll more "automatically".

  postulate
    contract
      : ∀ P pre
        → (C₁ true → P (inj₁ fakeErr) pre [])
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
        → P (inj₁ fakeErr) pre []
        → (∀ voteData → P (inj₂ voteData) pre [])
        → RWST-weakestPre (extensionCheckM voteProposal) P unit pre

module ConstructLedgerInfoM (proposedBlock : Block) (consensusDataHash : HashValue) where
  postulate
    contract
      : ∀ P pre
        → P (inj₁ fakeErr) pre []
        → (∀ ledgerInfo → P (inj₂ ledgerInfo) pre [])
        → RWST-weakestPre (constructLedgerInfoM proposedBlock consensusDataHash) P unit pre

module VerifyEpochM (epoch : Epoch) (safetyData : SafetyData) where
  contract
    : ∀ P pre
      → P (inj₁ fakeErr) pre []
      → P (inj₂ unit) pre []
      → RWST-weakestPre (verifyEpochM epoch safetyData) P unit pre
  proj₁ (contract Post pre b o) _ = b
  proj₂ (contract Post pre b o) _ = o


module VerifyAndUpdateLastVoteRoundM (round : Round) (safetyData : SafetyData) where
  C₁ = ⌊ round >? (safetyData ^∙ sdLastVotedRound) ⌋ ≡_
  safetyData≡ = (safetyData & sdLastVotedRound ∙~ round) ≡_

  contract
    : ∀ P pre
      → (C₁ false → P (inj₁ fakeErr) pre [])
      → (C₁ true → P (inj₂ (safetyData & sdLastVotedRound ∙~ round)) pre [])
      → RWST-weakestPre (verifyAndUpdateLastVoteRoundM round safetyData) P unit pre
  proj₁ (contract P₁ pre b o) c₁t = o c₁t
  proj₂ (contract P₁ pre b o) c₁f = b c₁f

module VerifyQcM (self : QuorumCert) where

  getVv = rmGetValidatorVerifier

  -- See comment on contract below to understand the motivation for stating and proving the property
  -- this way.

  P' : RoundManager → RWST-Post Output RoundManager (Either FakeErr Unit)
  P' pre = (λ { (Left x)  post outs → LBFT-NoEffect pre post outs
              ; (Right _) post outs → LBFT-NoEffect pre post outs
                                    × QuorumCertProps.Contract self (getVv pre) })

  contract' : ∀ pre → RWST-weakestPre (verifyQcM self) (P' pre) unit pre
  contract' pre _vv ._
     with self ^∙ qcSignedLedgerInfo ∙ liwsLedgerInfo ∙ liConsensusDataHash == hashVD (self ^∙ qcVoteData)
  ...| no neq = refl , refl
  ...| yes refl
     with self ^∙ qcCertifiedBlock ∙ biRound == 0
  ...| yes refl
     with self ^∙ qcParentBlock == self ^∙ qcCertifiedBlock
  ...| no neq = refl , refl
  ...| yes refl
     with self ^∙ qcCertifiedBlock == self ^∙ qcLedgerInfo ∙ liwsLedgerInfo ∙ liCommitInfo
  ...| no neq = refl , refl
  ...| yes refl
     with Map.kvm-size (self ^∙ qcLedgerInfo ∙ liwsSignatures) == 0
  ...| no neq = refl , refl
  ...| yes noSigs = (refl , refl) , record { lihash≡ = refl
                                           ; rnd0    = λ _ → record { par≡cert = refl
                                                                    ; cert≡li = refl
                                                                    ; noSigs = noSigs }
                                           ; ¬rnd0   = λ x → ⊥-elim (x refl) }
  contract' pre vv refl
     | yes refl
     | no neq
     with  LedgerInfoWithSignatures.verifySignatures (self ^∙ qcLedgerInfo)  vv | inspect
          (LedgerInfoWithSignatures.verifySignatures (self ^∙ qcLedgerInfo)) vv
  ...| Left e     | _ = refl , refl
  ...| Right unit | [ R ]
     with VoteData.verify (self ^∙ qcVoteData) | inspect
          VoteData.verify (self ^∙ qcVoteData)
  ...| Left e     | _ = refl , refl
  ...| Right unit | [ R' ] = (refl , refl)
                           , record { lihash≡ = refl
                                    ; rnd0    = ⊥-elim ∘ neq
                                    ; ¬rnd0   = λ _ → record { sigProp = R
                                                             ; vdProp = VotaDataProps.contract (self ^∙ qcVoteData) R' } }

  -- Suppose verifyQcM runs from prestate pre, and we wish to ensure that postcondition Post holds
  -- afterwards.  If P holds provided verifyQcM does not modify the state and does not produce any
  -- Outputs, and, if verifyQcM succeeds (returns Right unit), P holds provided
  -- QuorumCertProps.Contract holds for the given QuorumCert and the ValidatorVerifier of the
  -- prestate, then verifyQcM ensures P holds.  Proving this directly is painful because it's
  -- difficult to construct a QuorumCertProps.Contract self (getVv pre) that Agda understands allows
  -- us to invoke the rPrf (condition on P in case verifyQcM succeeds).  Therefore, we restate the
  -- conditions on P (as P', above) and prove that P' implies P, and then use RWST-impl to achieve
  -- the desired result.

  contract
    : ∀ P pre
    → (∀ {e} → P (Left e) pre [])
    → (QuorumCertProps.Contract self (getVv pre) → P (Right unit) pre [])
    → RWST-weakestPre (verifyQcM self) P unit pre
  contract Post pre lPrf rPrf = RWST-impl (P' pre) Post
                                       (λ { (Left x₁) st outs (refl , refl)            → lPrf
                                          ; (Right unit) st outs ((refl , refl) , prf) → rPrf prf })
                                       (verifyQcM self) unit pre (contract' pre)

module ConstructAndSignVoteM where
  VoteSrcCorrect : RoundManager → (FakeErr ⊎ Vote) → RoundManager → Set
  VoteSrcCorrect pre (inj₁ _) post = Unit
  VoteSrcCorrect pre (inj₂ v) post = VoteSrcCorrectCod pre post v

  record Contract (pre : RoundManager) (r : FakeErr ⊎ Vote) (post : RoundManager) (outs : List Output) : Set where
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
        : ∀ rm pre safetyData1 voteData ledgerInfo →
          (RWST-weakestPre (step₃ safetyData1 voteData author ledgerInfo)
                           (Contract rm))
                           unit pre
    step₃-contract rm pre safetyData1 voteData ledgerInfo

    {-
    The proof can be as simple as this:

       = λ _ _ _ _ → mkContract refl (mvsNew refl)

    Easy, right?!  Oh, you want a little more detail?  Sure here you go:

       = λ where .pre refl →
                  λ where .unit refl →
                           mkContract refl (mvsNew refl)   -- Indenting important for parsing

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
       (Contract rm))
      pre pre []

   It looks a bit ugly, but if we use C-u C-c C-, we get a more
   readable version that is exactly what we expect:

     RWST-weakestPre (step₃ safetyData1 voteData author ledgerInfo)
                     (Contract rm)
                     unit pre

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
      (Contract rm)                                                              = P
      unit                                                                       = ev
      pre                                                                        = st

   Applying the definition of RWST-weakestPre (RWST-bind...), we need:

     RWST-weakestPre
       (RWST-bind
            (RWST-gets id)                                                                 = m
            (λ st → RWST-put (st & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))) = f
       (RWST-weakestPre-bindPost unit                                                      = P
         (λ _ → RWST-return (inj₂ vote))
         (Contract rm))
       unit                                                                                = ev
       pre                                                                                 = pre

   Applying the definition of RWST-weakestPre (RWST-bind...) again, we have:

     RWST-weakestPre
       (RWST-gets id)
       (RWST-weakestPre-bindPost unit                                            = P
         (λ st → RWST-put (st & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote")))
         (RWST-weakestPre-bindPost unit
           (λ _ → RWST-return (inj₂ vote))
           (Contract rm)))
       unit                                                                      = ev
       pre                                                                       = pre

   Now applying the definition of RWST-weakestPre RWST-gets, we want:

     (RWST-weakestPre-bindPost
         unit                                                                           = ev
         (λ st → RWST-put (st & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))) = f
         (RWST-weakestPre-bindPost unit                                                 = Post
           (λ _ → RWST-return (inj₂ "vote"))
           (Contract rm)))
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
             (Contract rm))
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
         (Contract rm) x post ([] ++ outs₁))
      unit pre

   We can see that this is a more precise version of what we have above (without the shorthand),
   repeated here:

       RWST-weakestPre
         (RWST-put (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))) = post
         (λ x post outs₁ → (RWST-weakestPre-bindPost unit                         = P
                             (λ _ → RWST-return (inj₂ "vote"))
                             (Contract rm)) x post ([] ++ outs₁))
         unit
         pre

   Next, we apply the definition of RWST-weakestPre (RWST-put ...)

      (λ x post outs₁ → (RWST-weakestPre-bindPost unit
                          (λ _ → RWST-return (inj₂ "vote"))
                          (Contract rm)) x post ([] ++ outs₁))
      unit
      (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))
      []

    Instantiating,

      RWST-weakestPre-bindPost
       unit                                                                   = ev
       (λ _ → RWST-return (inj₂ "vote"))                                      = f
       (Contract rm)                                                          = Post
       unit                                                                   = x
       (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))          = post
       ([] ++ []))                                                            = outs

    Applying the definition of RWST-weakestPre-bindPost once again, we have:

      ∀ r → r ≡ unit → RWST-weakestPre
                         (RWST-return (inj₂ "vote"))
                         (RWST-Post++
                           (Contract rm)                                      = P
                           ([] ++ [])))                                       = outs
                         unit
                         (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))

    And applying the definition of RWST-Post++ yields:

      ∀ r → r ≡ unit → RWST-weakestPre
                         (RWST-return (inj₂ "vote"))
                         (λ x post outs₁ → VotesCorrect rm x post ([] ++ [] ++ outs₁))
                         unit
                         (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))

    Peeling off another couple of parameters (the first must be unit because of the second):
 -}

                      λ where .unit refl →


 {-

 The goal now looks like (using C-c C-,):

    Contract rm
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

    Contract rm
      (inj₂ "vote")
      (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))
      []

 Or (using C-u C-c C-,), we have the following goal:

    RWST-weakestPre
      (RWST-return
       (inj₂
        (Vote.newWithSignature voteData author ledgerInfo
         (ValidatorSigner.sign validatorSigner ledgerInfo))))
      (λ x post outs₁ → Contract rm x post (([] ++ []) ++ outs₁)) unit
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
       (λ x post outs₁ → Contract rm x post ([] ++ [] ++ outs₁))         = P
       unit                                                              = ev
       (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))     = pre

   Again, this looks like what we expect from above, so we can press
   on.  Now, applying the definition of RWST-weakestPre (RWST-return ...):

     (λ x post outs₁ → Contract rm x post ([] ++ [] ++ outs₁))
        (RWST-return (inj₂ "vote"))
        (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))
        []

   To prove this, we need to provide two proofs to mkContract, the first of which (for noOutput)
   is simply [] ++ [] ++ [] ≡ [], which is easily dispatched with refl.

   The other is

     VoteSrcCorrect
       rm                                                                = pre
       (inj₂ "vote")                                                     = inj₂ mv
       (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))     = post
       ([] ++ [] ++ []))                                                 = outs

   By definition of VoteSrcCorrect, we have:

        VoteSrcCorrectCod
          rm                                                             = pre
          (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote"))  = post
          "vote"

   Because the post state is achieved by update the sdLastVote field to vote, we can easily fulfil
   the requirements of the mvsNew constructor, namely:

        just "vote" ≡ (pre & lSafetyData ∙~ ("safetyData1" & sdLastVote ?~ "vote")) ^∙ lSafetyData ∙ sdLastVote

        Which easily holds by definition of ?~, regardless of pre.

   Thus, the proof now really is simple:

   -}

                               mkContract refl (mvsNew refl)

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

    open constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0

    contract
      : ∀ pre
        → RWST-weakestPre
            (constructAndSignVoteM-continue1 voteProposal validatorSigner proposedBlock safetyData0)
            (Contract pre) unit pre
    contract pre =
      VerifyQcM.contract (proposedBlock ^∙ bQuorumCert)
        (RWST-weakestPre-ebindPost unit (λ _ → step₁) (Contract pre)) pre
          (mkContract refl unit)
          λ where
            _ unit _ validatorVerifier _ →
              either {C = λ x → RWST-weakestPre (pure x ∙?∙ (λ _ → step₃)) (Contract pre) _ _}
                (λ _ → mkContract refl unit)
                (λ where
                  unit unit _ →
                    VerifyAndUpdatePreferredRoundM.contract (proposedBlock ^∙ bQuorumCert) safetyData0
                    (RWST-weakestPre-ebindPost unit (constructAndSignVoteM-continue2 voteProposal validatorSigner proposedBlock) _) pre
                    (λ _ → mkContract refl unit)
                    (λ _ →
                      -- Though this appears repetitive now, in the future the
                      -- contract will likely be refined to consider when and
                      -- how the preferred round is updated.
                      (λ twoChainRound>preferredRound safetyData1 safetyData1≡ →
                         Continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre pre)
                      , ((λ twoChainRound<preferredRound safetyData1 safetyData1≡ →
                         Continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre pre)
                      , (λ twoChainRound=preferredRound safetyData1 safetyData1≡ →
                         Continue2.contract voteProposal validatorSigner proposedBlock safetyData1 pre pre))))
                (Block.validateSignature proposedBlock validatorVerifier)

  module Continue0 (voteProposal : VoteProposal) (validatorSigner : ValidatorSigner) where
    open constructAndSignVoteM-continue0 voteProposal validatorSigner

    contract
      : ∀ pre
        → RWST-weakestPre (constructAndSignVoteM-continue0 voteProposal validatorSigner)
            (Contract pre) unit pre
    contract pre safetyData0@._ refl =
      VerifyEpochM.contract (proposedBlock ^∙ bEpoch) safetyData0
        (RWST-weakestPre-ebindPost unit (λ _ → step₁ safetyData0) (Contract pre)) pre
          (mkContract refl unit)
          λ where
            unit _ →
              (λ ≡nothing → Continue1.contract voteProposal validatorSigner proposedBlock safetyData0 pre)
              , λ where
                vote@._ refl →
                  (λ vote≡lastVote → mkContract refl (mvsLastVote refl refl))
                  , λ vote≢lastVote → Continue1.contract voteProposal validatorSigner proposedBlock safetyData0 pre

  module _ (maybeSignedVoteProposal : MaybeSignedVoteProposal) where

    voteProposal = maybeSignedVoteProposal ^∙ msvpVoteProposal

    contract : ∀ pre → RWST-weakestPre (constructAndSignVoteM maybeSignedVoteProposal) (Contract pre) unit pre
    contract pre nothing vs≡ = mkContract refl unit
    contract pre (just validatorSigner) vs≡ = Continue0.contract voteProposal validatorSigner pre

    contract⇒ : ∀ pre Post
                → (∀ r st outs → Contract pre r st outs → Post r st outs)
                → RWST-weakestPre (constructAndSignVoteM maybeSignedVoteProposal) Post unit pre
    contract⇒ pre Post impl =
      RWST-impl (Contract pre) Post impl
        (constructAndSignVoteM maybeSignedVoteProposal) unit pre
        (contract pre)
