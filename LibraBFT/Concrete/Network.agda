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

  record NetworkMsg : Set where
    constructor msg
    field
      dest    : NetworkAddr
      content : NetworkRecord 
  open NetworkMsg public
  
  sender : NetworkMsg → NodeId
  sender m = netrecAuthor (content m)
  

