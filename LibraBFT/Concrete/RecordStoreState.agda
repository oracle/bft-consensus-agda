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
  open import LibraBFT.Abstract.Records.Extends             hash hash-cr ec 
  open import LibraBFT.Abstract.RecordChain                 hash hash-cr ec
  open import LibraBFT.Abstract.RecordStoreState            hash hash-cr ec
  import      LibraBFT.Abstract.RecordStoreState.Invariants hash hash-cr ec
    as AbstractI

  -- VCM: I'm simplifying this abruptly; we should only
  --      add fields here as needed
  record RecordStoreState : Set where
    constructor mkRecordStoreState
    field
      -- rssInitiaState       : State
      rssPool                 : HashMap Hash Record
      rssCurrentRound         : Round
      rssCurrentVotes         : HashMap (Author ec) Vote
  open RecordStoreState

  _∈RSS_ : Record → RecordStoreState → Set
  (I _) ∈RSS rs = ⊥ -- The initial record is not really *in* the record store,
  (B x) ∈RSS rs = hash (encodeR (B x)) ∈HM (rssPool rs)
  (Q x) ∈RSS rs = hash (encodeR (Q x)) ∈HM (rssPool rs)

  ∈RSS-correct : (rss : RecordStoreState)(r : Record)
               → r ∈RSS rss → rssPool rss (hash (encodeR r)) ≡ just r
  ∈RSS-correct rss (B x) (v , prf) = {!!} -- VCM: We'll have to do some magic with hashes here
  ∈RSS-correct rss (Q x) (v , prf) = {!!}

  ∈RSS-correct-⊥ : (rss : RecordStoreState)(r : Record)
                 → r ∈RSS rss → rssPool rss (hash (encodeR r)) ≡ nothing → ⊥
  ∈RSS-correct-⊥ = {!!}


  ∈RSS-irrelevant : ∀{r rss}(p₀ p₁ : r ∈RSS rss) → p₀ ≡ p₁
  ∈RSS-irrelevant {I x} ()
  ∈RSS-irrelevant {B x} {st} p0 p1     
    = ∈HM-irrelevant (hash (encodeR (B x))) (rssPool st) p0 p1
  ∈RSS-irrelevant {Q x} {st} p0 p1    
    = ∈HM-irrelevant (hash (encodeR (Q x))) (rssPool st) p0 p1

  instance
    abstractRSS : isRecordStoreState RecordStoreState
    abstractRSS = record
      { isInPool            = _∈RSS_ 
      ; isInPool-irrelevant = ∈RSS-irrelevant
      }

  --------------------
  -- The Invariants --
  --------------------

  Correct : RecordStoreState → Set
  Correct st = AbstractI.Correct st

  IncreasingRound : RecordStoreState → Set
  IncreasingRound st = AbstractI.IncreasingRoundRule st

  VotesOnlyOnce : RecordStoreState → Set
  VotesOnlyOnce st = AbstractI.VotesOnlyOnceRule st

  LockedRound : RecordStoreState → Set₁
  LockedRound st = AbstractI.LockedRoundRule st

  -- A Valid Record Store State is one where all
  -- the invariants are respected.
  record ValidRSS (rss : RecordStoreState) : Set₁ where
    constructor valid-rss
    field
      correct           : Correct rss
      incr-round-rule   : IncreasingRound rss
      votes-once-rule   : VotesOnlyOnce rss
      locked-round-rule : LockedRound rss

  ---------------------
  -- The Empty State --
  ---------------------

  emptyRSS : RecordStoreState
  emptyRSS = record {
     -- ; rssInitial              = init
       -- rssInitiaState   : State
       rssPool                 = emptyHM
     ; rssCurrentRound         = 1
     ; rssCurrentVotes         = emptyHM
    }

  -- And now this is really trivial
  emptyRSS-valid : ValidRSS emptyRSS 
  emptyRSS-valid = 
    valid-rss (λ { (I _) () })
              (λ { α hα () q'∈P va va' x }) 
              (λ { α hα () q'∈P va va' x })
              (λ { α hα c2 vα (WithRSS.step rc' x {()}) vα' x₁ })

  --------------------------------
  -- Syntatically Valid Records --

  data NetworkRecord : Set where
    B : BBlock NodeId → NetworkRecord
    Q : BQC    NodeId → NetworkRecord
    --- ...

  -- Employ structural checks on the records when receiving
  -- them on the wire.
  check-signature-and-format : Signed NetworkRecord → Maybe Record
  check-signature-and-format = {!!}

  --------------------------------
  -- Semantically Valid Records --

  -- A record extends some other in a state if there exists
  -- a record chain in said state that ends on the record supposed
  -- to be extended
  data Extends (rss : RecordStoreState) : Record → Set where
     -- VCM: We might carry more information on this constructor
     extends : ∀{r r'} → WithRSS.RecordChain rss r 
             → r ← r' → Extends rss r'

  -- 'Extends' must be a decidable; We decide whether a record
  -- exnteds the state by performing the necessary checks.
  -- We might need to pass in an 'ValidRSS rss' argument here

  -- VCM: Looks like we will need some sort of DSL to
  -- be able to assemble this function in a reasonably readable way...
  extends? : (rss : RecordStoreState)(r : Record) → Dec (Extends rss r)
  extends? rss (I _) = no (λ { (extends _ ()) })
  extends? rss (B b)
    with bPrevQCHash b ≟Hash HashR (I mkInitial)
  ...| yes prf = yes (extends WithRSS.empty
                              (I←B {!!} (sym prf))) -- TODO: Check round?
  ...| no not-init
    with rssPool rss (bPrevQCHash b) | inspect (rssPool rss) (bPrevQCHash b)
  ...| nothing | [ R ] 
     = no (λ { (extends rc (I←B h r))                        → not-init (sym r) 
             ; (extends (WithRSS.step {_} {q} _ _ {∈rss}) (Q←B h r)) 
                  → ∈RSS-correct-⊥ rss q ∈rss (trans (cong (rssPool rss) r) R)
             })
  ...| just r | [ R ] = {!!}
  extends? rss (Q q) = {!!}


  --------------------------
  -- Insertion of Records --

  insert : (rss : RecordStoreState)(r : Record) → Extends rss r
         -- ValidRSS rss ?
         → RecordStoreState
  insert = {!!} 

  insert-ok : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidRSS rss
            → ValidRSS (insert rss r ext)
  insert-ok = {!!}
