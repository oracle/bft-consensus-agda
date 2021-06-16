open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Base.KVMap
open import LibraBFT.Base.PKCS
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Handle
open import LibraBFT.Impl.Handle.Properties
open import LibraBFT.Concrete.System.Parameters
open        EpochConfig
open import LibraBFT.Concrete.System
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})


module LibraBFT.Concrete.Properties.Common
 where

 record VoteForRound∈ (pk : PK)(round : ℕ)(epoch : ℕ)(bId : HashValue)(pool : SentMessages) : Set where
   constructor mkVoteForRound∈
   field
     msgWhole  : NetworkMsg
     msgVote   : Vote
     msg⊆      : msgVote ⊂Msg msgWhole
     msgSender : ℕ
     msg∈pool  : (msgSender , msgWhole) ∈ pool
     msgSigned : WithVerSig pk msgVote
     msgEpoch≡ : msgVote ^∙ vEpoch ≡ epoch
     msgRound≡ : msgVote ^∙ vRound ≡ round
     msgBId≡   : msgVote ^∙ vProposedId ≡ bId
 open VoteForRound∈ public

 module ConcreteCommonProperties (st : SystemState) (r  : ReachableSystemState st) where

   open PerState st r

   msgSentB4⇒VoteRound∈ : ∀ {v pk pool}
                         → (vv : WithVerSig pk v)
                         → (m : MsgWithSig∈ pk (ver-signature vv) pool)
                         → VoteForRound∈ pk (v ^∙ vRound) (v ^∙ vEpoch) (v ^∙ vProposedId) pool
   msgSentB4⇒VoteRound∈ {v} vv m
       with sameSig⇒sameVoteDataNoCol (msgSigned m) vv (msgSameSig m)
   ... | refl = mkVoteForRound∈ (msgWhole m) (msgPart m) (msg⊆ m) (msgSender m)
                                (msg∈pool m) (msgSigned m) refl refl refl

   ¬Gen∧Round≡⇒¬Gen : ∀ {v pk round epoch bId} {st : SystemState}
                     → ReachableSystemState st
                     → Meta-Honest-PK pk
                     → (vfr : VoteForRound∈ pk round epoch bId (msgPool st))
                     → ¬ (∈GenInfo (ver-signature (msgSigned vfr)))
                     → (sig : WithVerSig pk v)
                     → v ^∙ vRound ≡ round
                     → ¬ (∈GenInfo (ver-signature sig))
   ¬Gen∧Round≡⇒¬Gen r pkH v₁ ¬genV₁ sigV₂ refl genV₂
      with ¬genVotesRound≢0 r pkH (msgSigned v₁) (msg⊆ v₁) (msg∈pool v₁) ¬genV₁
   ...| v₁r≢0 = ⊥-elim (v₁r≢0 (trans (msgRound≡ v₁) (genVotesRound≡0 sigV₂ genV₂)))
