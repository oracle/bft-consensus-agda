open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

module LibraBFT.Concrete.Records where

  -- All the other records will draw their authors from
  -- a given Set. They are named with a 'B' prefix standing for
  -- 'Basic' records.
  record Block  : Set where
    constructor mkBlock
    field
      bEpochId    : EpochId
      bAuthor     : NodeId
      bCommand    : Command
      bPrevQCHash : QCHash
      bRound      : Round
  open Block public

  record Vote  : Set where
    constructor mkVote
    field
      vEpochId   : EpochId
      vAuthor    : NodeId
      vBlockHash : BlockHash
      vRound     : Round
      --vState     : State
  open Vote public

  record QC (votes : Set) : Set where
   field
     qEpochId       : EpochId
     qAuthor        : NodeId
     qBlockHash     : BlockHash
     qRound         : Round
     qVotes         : List votes
     --qState         : State
  open QC public

  record Timeout : Set where
    constructor mkTimeout
    field
      toAuthor  : NodeId
      toRound   : Round
  open Timeout public

  -- This is a notification of a commit.  It will probably have something different in it.
  record CN : Set where
    constructor mkCommitMsg
    field
      cEpochId : EpochId
      cAuthor  : NodeId
      cRound   : Round
      cCert    : QCHash
  open CN public

  postulate
   instance
     encBlock  : Encoder Block 
     encVote   : Encoder Vote
     encQC     : ∀{V}⦃ encV : Encoder V ⦄ → Encoder (QC V)
     encCN     : Encoder CN
     encTO     : Encoder Timeout

  --------------------------
  -- Easy Field Accessors --

  record IsLibraBFTRecord (A : Set) : Set where
    constructor is-librabft-record
    field
      getAuthor : A → NodeId
      getRound  : A → Round
      getPrev   : A → Hash
      getEpoch  : A → EpochId
  open IsLibraBFTRecord {{...}} public

  instance
    ibrBlock : IsLibraBFTRecord Block
    ibrBlock = is-librabft-record bAuthor bRound bPrevQCHash bEpochId

    ibrQC : ∀{V} → IsLibraBFTRecord (QC V)
    ibrQC = is-librabft-record qAuthor qRound qBlockHash qEpochId

    ibrCN : IsLibraBFTRecord CN
    ibrCN = is-librabft-record cAuthor cRound cCert cEpochId

    ibrVote : IsLibraBFTRecord Vote
    ibrVote = is-librabft-record vAuthor vRound vBlockHash vEpochId

    ibrSigned : ∀{X}⦃ ibr : IsLibraBFTRecord X ⦄ ⦃ encX : Encoder X ⦄ → IsLibraBFTRecord (Signed X)
    ibrSigned ⦃ is-librabft-record a b c d ⦄
      = is-librabft-record (a ∘ content) (b ∘ content) (c ∘ content) (d ∘ content)

    ibrVSigned : ∀{X}⦃ ibr : IsLibraBFTRecord X ⦄ ⦃ encX : Encoder X ⦄ → IsLibraBFTRecord (VerSigned X)
    ibrVSigned ⦃ is-librabft-record a b c d ⦄
      = is-librabft-record (a ∘ content) (b ∘ content) (c ∘ content) (d ∘ content)

  ----------------------
  -- Verified Records --
  
  -- Note that besides verification of signatures, we also
  -- prove that the author belongs in a set of valid authors
  module VerifiedRecords (ec : EpochConfig)(pki : PKI ec) where

   data Record : Set where
     B : ∀{α} (r : VerSigned Block)
       → isAuthor pki (getAuthor r) ≡ just α
       → verWithPK r ≡ pkAuthor pki α
       → Record
     V : ∀{α} (r : VerSigned Vote)                 
       → isAuthor pki (getAuthor r) ≡ just α
       → verWithPK r ≡ pkAuthor pki α
       → Record
     Q : ∀{α} (r : VerSigned (QC (VerSigned Vote))) 
       → isAuthor pki (getAuthor r) ≡ just α
       → verWithPK r ≡ pkAuthor pki α
       → Record
     C : ∀{α} (r : VerSigned CN)                    
       → isAuthor pki (getAuthor r) ≡ just α
       → verWithPK r ≡ pkAuthor pki α
       → Record
     T : ∀{α} (r : VerSigned Timeout)               
       → isAuthor pki (toAuthor (content r)) ≡ just α
       → verWithPK r ≡ pkAuthor pki α
       → Record

   -- VCM: LibraBFT.Concrete.RecordStoreState.HashR, which hashes
   --      a record, is defined in terms of this encoder.
   --      This is why we explicitely REMOVE the signature from
   --      this bytestring or define HashR differently.
   --      The end of Section 4.1 (libra v1 paper) indicates 
   --      signatures are /not/ part of the hash of records.
   encodeRecord : Record → ByteString
   encodeRecord (B r _ _) = encode (content r)
   encodeRecord (V r _ _) = encode (content r)
   encodeRecord (Q r _ _) = encode (content r)
   encodeRecord (C r _ _) = encode (content r)
   encodeRecord (T r _ _) = encode (content r)

   vrAuthor : Record → Author ec
   vrAuthor (B {α} _ _ _) = α
   vrAuthor (V {α} _ _ _) = α
   vrAuthor (Q {α} _ _ _) = α
   vrAuthor (C {α} _ _ _) = α
   vrAuthor (T {α} _ _ _) = α


{-
  ------------------------------------------------------------
  -- Abstraction of Storeable Records into Abstract Records --


  -- BlockRecords are what we will be storing in block storage;
  data BlockRecord : Set where
    B : Block            → BlockRecord
    Q : QC (Signed Vote) → BlockRecord

  postulate
    instance
      encR : Encoder BlockRecord  

  module Abstraction 
     (hash    : ByteString → Hash)
     (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
     (ec      : EpochConfig)
    where

   import LibraBFT.Abstract.Records ec Hash as Abs
 
   hashBR : BlockRecord → Hash
   hashBR = hash ∘ encode

   abs : BlockRecord → Abs.Record
   abs br = {!!}
-}
