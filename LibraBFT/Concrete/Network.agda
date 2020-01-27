{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types

open import LibraBFT.Concrete.Records

module LibraBFT.Concrete.Network where

-- VCM-QUESTION: This whole module goes byebye with the
-- mirror of our Haskell proto. The Haskell proto
-- sends two messages; a VoteMsg and a ProposalMsg, it seems
-- like the check-format-and-verify will return a 
-- a proof that these messages have been correctly signed
-- by a valid author, etc, etc...

-- MSM: Not quite.  You are talking 

{-
  ----------------------
  -- Network Messages --
  ----------------------

  data NetworkRecord : Set where
    B : Signed BlockProposal      → NetworkRecord
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
  
  -----------------------------------
  -- Valid Records Depend on Epoch --

  -- The 'check-signature-and-format functio is responsible for
  -- employing the necessary structural checks on the messages
  -- we received from the network. 
  module _ (ec : EpochConfig)(pki : PKI ec) where
   
   open VerifiedRecords ec pki

   -- Employ structural checks on the records when receiving them on the wire.
   check-signature-and-format : NetworkRecord → Maybe Record
   check-signature-and-format (V nv) 
   -- Is the author of the vote an actual author?
     with isAuthor pki (getAuthor nv) | inspect (isAuthor pki) (getAuthor nv)
   -- 1; No! Reject!
   ...| nothing | _ = nothing
   -- 2; Yes! Now we must check whether the signature matches
   ...| just α  | [ Valid ]
     with checkSignature-prf (pkAuthor pki α) nv
   ...| nothing = nothing
   ...| just (res , prf1 , refl) = just (V res Valid prf1)

   check-signature-and-format (B nb) = {!!}
   check-signature-and-format (Q nq) = {!!}
   check-signature-and-format (C nc) = {!!}
   check-signature-and-format (T nc) = {!!}
-}
