open import LibraBFT.Prelude
  hiding (lookup)
open import LibraBFT.BasicTypes
open import LibraBFT.Hash
open import LibraBFT.Lemmas

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

  hashRecord : Record → Hash
  hashRecord = hash ∘ encodeR

  open import LibraBFT.Concrete.Util.HashSet hashRecord

  -- VCM: I'm simplifying this abruptly; we should only
  --      add fields here as needed
  record RecordStoreState : Set where
    constructor mkRecordStoreState
    field
      -- rssInitiaState       : State
      rssPool                 : HashSet
      rssCurrentRound         : Round
      -- rssCurrentVotes         : HashMap (Author ec) Vote
  open RecordStoreState

  _∈RSS_ : Record → RecordStoreState → Set
  (I _) ∈RSS rs = Unit -- The initial record is not really *in* the record store,
  (B x) ∈RSS rs = (B x) ∈HS (rssPool rs)
  (Q x) ∈RSS rs = (Q x) ∈HS (rssPool rs)

  _∈RSS?_ : (r : Record)(rss : RecordStoreState) → Dec (r ∈RSS rss)
  (I _) ∈RSS? rss = yes unit
  (B b) ∈RSS? rss = (B b) ∈HS? (rssPool rss)
  (Q b) ∈RSS? rss = (Q b) ∈HS? (rssPool rss)

{-
  ∈RSS-correct : (rss : RecordStoreState)(r : Record)
               → r ∈RSS rss → lookup (rssPool rss) (hashRecord r) ≡ just r
  ∈RSS-correct rss (B x) prf = lookup-correct (B x) (rssPool rss) prf
  ∈RSS-correct rss (Q x) prf = lookup-correct (Q x) (rssPool rss) prf

  ∈RSS-correct-⊥ : (rss : RecordStoreState)(r : Record)
                 → r ∈RSS rss → lookup (rssPool rss) (hashRecord r) ≡ nothing → ⊥
  ∈RSS-correct-⊥ = {!!}
-}


  ∈RSS-irrelevant : ∀{r rss}(p₀ p₁ : r ∈RSS rss) → p₀ ≡ p₁
  ∈RSS-irrelevant {I x} unit unit = refl
  ∈RSS-irrelevant {B x} {st} p0 p1     
    = ∈HS-irrelevant (B x) (rssPool st) p0 p1
  ∈RSS-irrelevant {Q x} {st} p0 p1    
    = ∈HS-irrelevant (Q x) (rssPool st) p0 p1

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
       rssPool                 = empty
     ; rssCurrentRound         = 1
     -- ; rssCurrentVotes         = empty
    }

  -- And now this is really trivial
  emptyRSS-valid : ValidRSS emptyRSS
  emptyRSS-valid =
    valid-rss (λ { (I mkInitial) _  → WithRSS.empty
                 ; (B _) abs → ⊥-elim (∈HS-empty-⊥ abs) 
                 ; (Q _) abs → ⊥-elim (∈HS-empty-⊥ abs)})
              (λ { _ _ abs _ _ _ _ → ⊥-elim (∈HS-empty-⊥ abs) })
              (λ { _ _ abs _ _ _ _ → ⊥-elim (∈HS-empty-⊥ abs) })
              (λ { _ _ _ _ (WithRSS.step _ _ {abs}) _ _ 
                 → ⊥-elim (∈HS-empty-⊥ abs) })

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
     extends : ∀{r r'}
             → (rInPool : r ∈RSS rss)
             -- We will not allow insertion of a Record whose hash
             -- collides with one already in the RecordStore.
             -- Otherwise we'll have to carry HashBroke around on
             -- most/all properties.
             → (r'New   : ¬ (r' ∈RSS rss))
             → r ← r'
             → Extends rss r'


{-
  -- MSM: Why is this needed?
  -- VCM: This is the function that should do all the checks and
  --      pass that through a proof object 'Extends'
  --      
  --
  -- 'Extends' must be a decidable; We decide whether a record
  -- exnteds the state by performing the necessary checks.
  -- We might need to pass in an 'ValidRSS rss' argument here
-}

  extends-Q? : (rss : RecordStoreState)(q : QC)
             → ¬ ((Q q) ∈RSS rss)
             → Maybe (Extends rss (Q q)) 
  extends-Q? rss q qNew = {!!}

  extends-B? : (rss : RecordStoreState)(b : Block)
             → ¬ ((B b) ∈RSS rss)
             → Maybe (Extends rss (B b)) 
  extends-B? rss b bNew 
  -- 1. Are we extending the initial record?
    with bPrevQCHash b ≟Hash hashRecord (I mkInitial)
  ...| yes refl  = just (extends {r = I mkInitial} unit bNew 
                                (I←B {!!} refl)) -- TODO: make the round check.
  ...| no  ¬Init
  -- 2. Ok, if not the initial, which one? We must look it up.
    with lookup (rssPool rss) (bPrevQCHash b)
       | inspect (lookup (rssPool rss)) (bPrevQCHash b)
  -- 2.1 case nothing was found, it does not extend.
  ...| nothing | [ R ] = nothing
  -- 2.2 case we found the initial contradicts the check at (1)
  ...| just (I mkInitial) | [ R ] 
     = ⊥-elim (¬Init (lookup-correct' (bPrevQCHash b) (rssPool rss) R))
  -- 2.3 case we found a block, it does not extend. Blocks only extend QC's
  ...| just (B _) | [ R ] = nothing
  -- 2.4 case we found a QC, it might extend
  ...| just (Q q) | [ R ] 
  -- 2.4.1 Is block round strictly greater than the QC it extends?
     with suc (qRound (qBase q)) ≤? bRound b
  -- 2.4.1.1 No; the rounds are not ok.
  ...| no round-nok = nothing
  -- 2.4.1.2 Yes, rounds are fine; So far, it extends.
  --         VCM: Shouldn't we perform additional checks?
  ...| yes round-ok = just (extends (lookup-correct'' _ _ R) bNew 
                             (Q←B {q} round-ok (sym (lookup-correct' _ _ R))))

  -- VCM: Looks like we will need some sort of DSL to
  -- be able to assemble this function in a reasonably readable way...
  extends? : (rss : RecordStoreState)(r : Record) → Maybe (Extends rss r)
  extends? rss r with r ∈RSS? rss
  ...| yes ¬rNew = nothing -- no (λ { (extends _ rNew _) → rNew ¬rNew })
  ...| no   rNew with r 
  ...| I i = nothing -- no (λ { (extends _ _ ()) })
  ...| B b = extends-B? rss b rNew
  ...| Q q = extends-Q? rss q rNew

  --------------------------
  -- Insertion of Records --

{-
  insert : (rss : RecordStoreState)(r′ : Record)(ext : Extends rss r′)
         → RecordStoreState
  insert rss r′ _ = {!!} -- record rss { rssPool = proj₁ (rssPool rss [ HashR r′ := just r′ , _≟Hash_ ]) }

  insert-ok-correct : (rss : RecordStoreState)(r′ : Record)(ext : Extends rss r′)
            → ValidRSS rss
            → Correct (insert rss r′ ext)
  insert-ok-correct rss r′ (extends {r} {r′} rInPool r←r′ r′NotInPool) vrss r₂ r₂∈post = {!!}
{-

If r₂ ∈RSS rss, then by (correct vrss), there is a RecordChain r₂, we need to prove the same
RecordChain works also for (insert rss r′ ext).

If ¬ (r₂ ∈RSS rss), then by r₂∈post and (something like) HashMap.onlyInsertOne, r₂ ≡ r′, so we can
use rInPool to find a RecordChain r, and extend it with r←r′ to construct the needed RecordChain.

-}

  -- NOTE: the following are mindlessly copied from insert-ok-correct, may not be what we want

  insert-ok-increasing-round : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidRSS rss
            → IncreasingRound (insert rss r ext)
  insert-ok-increasing-round rss r ext vrss = {!!}

  insert-ok-votes-only-once : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidRSS rss
            → VotesOnlyOnce (insert rss r ext)
  insert-ok-votes-only-once rss r ext vrss = {!!}

  insert-ok-locked-round : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidRSS rss
            → LockedRound (insert rss r ext)
  insert-ok-locked-round rss r ext vrss = {!!}

  insert-ok : (rss : RecordStoreState)(r : Record)(ext : Extends rss r)
            → ValidRSS rss
            → ValidRSS (insert rss r ext)
  insert-ok rss r ext vrss =
    valid-rss
      (insert-ok-correct          rss r ext vrss)
      (insert-ok-increasing-round rss r ext vrss)
      (insert-ok-votes-only-once  rss r ext vrss)
      (insert-ok-locked-round     rss r ext vrss)
-}
