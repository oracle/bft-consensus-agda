{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Abstract.Records

module LibraBFT.Concrete.Network where

  --------------------------------
  -- Syntatically Valid Records --

  data NetworkRecord : Set where
    B : Signed (BBlock NodeId)                      → NetworkRecord
    V : Signed (BVote NodeId)                       → NetworkRecord
    Q : Signed (BQC NodeId (Signed (BVote NodeId))) → NetworkRecord
    C : Signed (BC NodeId)                          → NetworkRecord
    --- ... TOFINISH

  netrecAuthor : NetworkRecord → NodeId
  netrecAuthor (B b) = bAuthor (content b)
  netrecAuthor (V b) = vAuthor (content b)
  netrecAuthor (Q b) = qAuthor (content b)
  netrecAuthor (C b) = cAuthor (content b)

  data NetworkAddr : Set where
    Broadcast : NetworkAddr
    Single    : NodeId → NetworkAddr

  -- TODO: Make a ClientReq be a network msg too
  record NetworkMsg : Set where
    constructor wire
    field
      dest    : NetworkAddr
      content : NetworkRecord 
  open NetworkMsg public
  
  sender : NetworkMsg → NodeId
  sender m = netrecAuthor (content m)
  
  ------------------------------------------------
  -- Syntatically Valid Records Depend on Epoch --

  module _ (ec : EpochConfig) where
   
   -- We need Encoder instances from here; 
   -- VCM: why doesn't "open import" work? weird!
   --   TODO: look into instance resolution docs
   import LibraBFT.Abstract.Records ec as R

   data VerNetworkRecord : Set where
     B : (vs : VerSigned (BBlock (Author ec)))
       → verWithPK vs ≡ pkAuthor ec (getAuthor vs)
       → VerNetworkRecord
     V : (vs : VerSigned (BVote (Author ec)))
       → verWithPK vs ≡ pkAuthor ec (getAuthor vs)
       → VerNetworkRecord
     C : (vs : VerSigned (BC (Author ec)))
       → verWithPK vs ≡ pkAuthor ec (getAuthor vs)
       → VerNetworkRecord
     -- ... TOFINISH

   -- Employ structural checks on the records when receiving them on the wire.
   check-signature-and-format : NetworkRecord → Maybe VerNetworkRecord
   check-signature-and-format (V nv) 
   -- Is the author of the vote an actual author?
     with isAuthor ec (vAuthor (content nv)) 
   -- 1; No! Reject!
   ...| nothing = nothing
   -- 2; Yes! Now we must check whether the signature matches
   ...| just α  
     with checkSignature-prf (pkAuthor ec α) (Signed-map (BVote-map (λ _ → α)) nv)
   ...| nothing = nothing
   ...| just (va , prf1 , refl) = just (V va prf1)

   check-signature-and-format (B nb) = {!!}
   check-signature-and-format (Q nq) = {!!}
   check-signature-and-format (C nc) = {!!}
