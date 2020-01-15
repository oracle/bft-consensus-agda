{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types

open import LibraBFT.Concrete.Records

module LibraBFT.Concrete.Network where

  --------------------------------
  -- Syntatically Valid Records --

  data NetworkRecord : Set where
    B : Signed Block              → NetworkRecord
    V : Signed Vote               → NetworkRecord
    Q : Signed (QC (Signed Vote)) → NetworkRecord
    T : Signed Timeout            → NetworkRecord
    C : Signed CN                 → NetworkRecord


  netrecAuthor : NetworkRecord → NodeId
  netrecAuthor (B b) = bAuthor (content b)
  netrecAuthor (V b) = vAuthor (content b)
  netrecAuthor (Q b) = qAuthor (content b)
  netrecAuthor (C b) = cAuthor (content b)
  netrecAuthor (T b) = toAuthor (content b)

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

  module _ {Author : Set}
           (isAuthor : NodeId → Maybe Author) 
           (pkAuthor : Author → PK) 
     where

   -- VCM: I apparently lost the connection between valid the verification
   --      of the signature being with the public key of the right author.
   --      Yet, here, it seems like this is implied by parametricity. 
   --      The only way of producing a PK is through pkAuthor, which
   --      depends on an abstract Author type; which in turn, can only be
   --      inhabited by isAuthor.

   data ValidAuthor (nid : NodeId) : Set where
     va : ∀{α} 
        → isAuthor nid ≡ just α
        → ValidAuthor nid

   -- Employ structural checks on the records when receiving them on the wire.
   check-signature-and-format : NetworkRecord → Maybe (ValidRecord ValidAuthor)
   check-signature-and-format (V nv) 
   -- Is the author of the vote an actual author?
     with isAuthor (getAuthor nv) | inspect isAuthor (getAuthor nv)
   -- 1; No! Reject!
   ...| nothing | _ = nothing
   -- 2; Yes! Now we must check whether the signature matches
   ...| just α  | [ Valid ]
     with checkSignature-prf (pkAuthor α) nv
   ...| nothing = nothing
   ...| just (res , prf1 , refl) = just (V res (va Valid))

   check-signature-and-format (B nb) = {!!}
   check-signature-and-format (Q nq) = {!!}
   check-signature-and-format (C nc) = {!!}
   check-signature-and-format (T nc) = {!!}
