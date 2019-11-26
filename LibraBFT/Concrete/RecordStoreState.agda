open import LibraBFT.Prelude
open import LibraBFT.BasicTypes
open import LibraBFT.Hash
open import LibraBFT.Lemmas

open import LibraBFT.Concrete.Util.HashMap

module LibraBFT.Concrete.RecordStoreState
    -- A Hash function maps a bytestring into a hash.
    (hash    : ByteString → Hash)
    -- And is colission resistant
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
    (ec : EpochConfig)
 where

  open import LibraBFT.Abstract.Records                                  ec 
  open import LibraBFT.Abstract.RecordChain                 hash hash-cr ec
  open import LibraBFT.Abstract.RecordStoreState            hash hash-cr ec
  import      LibraBFT.Abstract.RecordStoreState.Invariants hash hash-cr ec
    as AbstractI

  -- VCM: We'll be having the mutable bit of the record store state 
  --      separate from the immutable one.
  record RecordStoreState : Set where
    constructor mkRecordStoreState
    field
      -- rssInitiaState       : State
      rssBlocks               : HashMap BlockHash (BBlock (Author ec))
      rssQCs                  : HashMap QCHash    (BQC    (Author ec))
      rssRoundToQChash        : HashMap Round QCHash
      rssCurrentProposedBlock : Maybe BlockHash
      rssHighestQCRound       : Round
      -- rssHighestTCRound    : Round
      rssCurrentRound         : Round
      -- rssHighest2ChainRound       : Round
      -- rssHighestCommittedRound    : Round
      -- rssHighestTimoutCertificate : Maybe (List Timeout)
      -- rssCurrentTimeouts      : HashMap authors Timeout
      rssCurrentVotes         : HashMap (Author ec) (BVote (Author ec))
      -- rssCurrentTimeoutWeight     : ℕ  -- LIBRA-DIFF: assume equal weights for now
      -- rssCurrentElection          : ?
  open RecordStoreState

  -- The initial record is not really *in* the record store,
  -- but the record store knows of it, since it has
  -- the epoch config. Hence, we'll just state that for the pusposes
  -- of the _←_ relation, there is an initial in there.
  --
  -- Recall that the initial record is proof irrelevant.
  _∈Mut_ : Record → RecordStoreState → Set
  (I _) ∈Mut rs = Unit
  (B x) ∈Mut rs = hash (encodeR (B x)) ∈HM (rssBlocks rs)
  (Q x) ∈Mut rs = hash (encodeR (Q x)) ∈HM (rssQCs rs)

  ∈Mut-irrelevant : ∀{r rss}(p₀ p₁ : r ∈Mut rss) → p₀ ≡ p₁
  ∈Mut-irrelevant {I x} unit unit = refl
  ∈Mut-irrelevant {B x} {st} p0 p1     
    = ∈HM-irrelevant (hash (encodeR (B x))) (rssBlocks st) p0 p1
  ∈Mut-irrelevant {Q x} {st} p0 p1    
    = ∈HM-irrelevant (hash (encodeR (Q x))) (rssQCs st) p0 p1

  abstractRSS : isRecordStoreState RecordStoreState
  abstractRSS = rss _∈Mut_ ∈Mut-irrelevant

  emptyRSS : RecordStoreState
  emptyRSS = record {
     -- ; rssInitial              = init
       -- rssInitiaState   : State
       rssBlocks               = emptyHM
     ; rssQCs                  = emptyHM
     ; rssRoundToQChash        = proj₁ (emptyHM [ 0 := just (ecInitialState ec) , _≟ℕ_ ])
     ; rssCurrentProposedBlock = nothing
     ; rssHighestQCRound       = 0
       -- rssHighestTCRound    = 0
     ; rssCurrentRound         = 1
       -- rssHighest2ChainRound   : Round
       -- rssHighestCommittedRound : Round
       -- rssHighestTimoutCertificate : Maybe (List Timeout)
     -- ; rssCurrentTimeouts      = emptyHM
     ; rssCurrentVotes         = emptyHM
       -- rssCurrentTimeoutWeight : ℕ  -- LIBRA-DIFF: assume equal weights for now
       -- rssCurrentElection : ?
    }

  ValidRSS : RecordStoreState → Set₁
  ValidRSS st = AbstractI.Correct (one-rss abstractRSS st)

  NoIncreasingRoundBroke : RecordStoreState → Set₁
  NoIncreasingRoundBroke st = AbstractI.IncreasingRoundRule (one-rss abstractRSS st)

  -- ... the other invariants are conjured the same

  -- And now this is really trivial
  emptyRSS-is-valid : ValidRSS emptyRSS 
  emptyRSS-is-valid (I _) r = WithRSS.empty
