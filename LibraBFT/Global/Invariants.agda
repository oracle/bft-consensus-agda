open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import Optics.All

module LibraBFT.Global.Invariants 
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

  open import LibraBFT.Concrete.Consensus.Types.EpochIndep
  open import LibraBFT.Concrete.NetworkMsg

  -- instead of postulating the whole system layer here, I'll
  -- just have a self-descriptive predicate. We can struggle to
  -- define this based on the system layer later.
  postulate 
    HasBeenSent : NetworkMsg → Set


-- VCM: I'm trying to understand how to sketch the proof that our implementation
-- will (hopefully! :) ) satisfy the abstract invariants. This has
-- been refactored to Global.BlockTreeInvariants because we need knowledge of
-- the all-knowing all-seeing system's layer.
-- 
-- Recalling my comment from Concrete.BlockTreeAbstraction:849, it is inline
-- with what Mark has been thinking.
-- 
--  -- TODO: Our algorithm will ensure we never cast a vote to a proposal
--  -- that references a round smaller than our previous round. We will need
--  -- a proof of that. Moreover, we'll later need someway to lift properties
--  -- from our own algorithm to another honest author... I need to think carefully
--  -- about this.
-- 
-- That is, we need a way to say "α follows the same algo because α is honest, hence,
-- the invariants apply to α"
--
-- I like Mark's idea of saying something in the lines of:
-- If I have a record in my state with a verified signature but I'm not
-- the author, then this must have been sent by someone.
--
-- r ∈ myState → WithVerSig r → author r ≢ me → ∃[msg] (msgRecord ≡ r ∧ HasBeenSent msg)
--
-- As we can see, however, there is a disconnect from records and messages.
-- Looking at the QuorumCertificate datatype, how do we make a WithVerSig Vote
-- from the list of votes? I have no idea!
-- We might have to keep the received messages and a proof that we checked
-- their signatures somewhere; I suspect that we might be able to pull this off
-- keepnig a proof that each vote in a QC has a WithVerSig in Consensus.Types.IsValidQC
--
-- Let's leave this problem for the future and move on, though.
--
-- The idea, taken from mark-property-musings, is that we will be able to
-- prove the invariants because honest peers also respect them, hence, when
-- we saw votes from α, they must have been sent by α, who runs the Concrete.Handle.handle,
-- Hence, properties about Concrete.Handle.handle translate to α.
--
-- Take the increasing round, for example, we need something like the following
-- property, which should be provided from the system layer:

  IncreasingRound : Set
  IncreasingRound 
    = ∀ {α v v'}
    → (ec1 : EpochConfig)
    → ∀ {αabs}
    → isAuthor ec1 α ≡ just αabs
    → Honest ec1 αabs
    → v  ^∙ vmVote ∙ vAuthor ≡ α → HasBeenSent (V v)  → WithVerSig v
    → v' ^∙ vmVote ∙ vAuthor ≡ α → HasBeenSent (V v') → WithVerSig v'
    → v  ^∙ vmProposed ∙ biEpoch ≡ v' ^∙ vmProposed ∙ biEpoch
    → unsafeReadMeta (v ^∙ vmVote ∙ vOrder) <VO unsafeReadMeta (v' ^∙ vmVote ∙ vOrder)
    → v ^∙ vmProposed ∙ biRound < v ^∙ vmProposed ∙ biRound

