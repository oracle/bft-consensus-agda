{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Abstract.Records

module LibraBFT.Concrete.NetworkMessages where

  --------------------------------
  -- Syntatically Valid Records --


  -- This is a notification of a commit.  It is a toy to enable developing the "big picture" linking
  -- the concrete model to the correctness condition.  It should eventually be made to reflect
  -- messages used to inform clients of commits in the real implementation.
  record Commit : Set where
    constructor mkCommitMsg
    field
      cEpochId : EpochId
      cAuthor  : NodeId
      cRound   : Round
      cCert    : QCHash
  open Commit public

  postulate
    instance
      encC      : Encoder Commit

  record IsLibraBFTMsg (A : Set) : Set where
    constructor is-librabft-msg
    field
      getAuthor   : A → NodeId
      getRound    : A → Round
      getPrevHash : A → QCHash
      getEpochId  : A → EpochId
  open IsLibraBFTMsg {{...}} public

  instance
    commit-is-record : IsLibraBFTMsg Commit
    commit-is-record = is-librabft-msg
      cAuthor
      cRound
      cCert
      cEpochId

  VSCommit : Set
  VSCommit = VerSigned Commit

  data NetworkRecord : Set where
    C : Signed Commit → NetworkRecord
    --- ... TOFINISH

  instance
    vsCommit-is-record : IsLibraBFTMsg VSCommit
    vsCommit-is-record = is-librabft-msg
      (cAuthor  ∘ content)
      (cRound   ∘ content)
      (cCert    ∘ content)
      (cEpochId ∘ content)

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

  postulate -- TODO: model properly
    pubKeyForNode : NodeId → PK

  data VerNetworkRecord : Set where
    C : (vs : VerSigned Commit)
      → verWithPK vs ≡ pubKeyForNode (cAuthor (content vs))
      → VerNetworkRecord
    -- ... TOFINISH

  -- Employ structural checks on the records when receiving them on the wire.
  check-signature-and-format : NetworkRecord → Maybe VerNetworkRecord
  check-signature-and-format (C nc)
    with (fakeEC (cEpochId (content nc))) -- TODO: model properly
  ...| ec
    with pubKeyForNode (cAuthor (content nc))
  ...| senderPK
  -- Is the author of the commit an actual author?
    with isAuthor ec (cAuthor (content nc))
  -- 1; No! Reject!
  ...| nothing = nothing
  -- 2; Yes! Now we must check whether the signature matches
  ...| just _
    with checkSignature-prf (pubKeyForNode (cAuthor (content nc))) nc
  ...| nothing = nothing
  ...| just (va , prf1 , prf2) rewrite (sym prf2) = just (C va prf1)

