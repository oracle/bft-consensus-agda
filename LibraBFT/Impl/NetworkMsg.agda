{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Lemmas
open import LibraBFT.Hash
open import LibraBFT.Base.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.Types.EpochIndep
open import LibraBFT.Impl.Util.Crypto

-- This module defines the types of messages that the implementation
-- can send, along with properties defining ways in which votes can be
-- represented in them, some useful functions, and definitions of how
-- NetworkMsgs are signed.

module LibraBFT.Impl.NetworkMsg where
  data NetworkMsg : Set where
    P : ProposalMsg → NetworkMsg
    V : VoteMsg     → NetworkMsg
    C : CommitMsg   → NetworkMsg

  P≢V : ∀ {p v} → P p ≢ V v
  P≢V ()

  C≢V : ∀ {c v} → C c ≢ V v
  C≢V ()

  V-inj : ∀ {vm1 vm2} → V vm1 ≡ V vm2 → vm1 ≡ vm2
  V-inj refl = refl

  -- What does it mean for a (concrete) Vote to be represented in a NetworkMsg?
  data _QC∈ProposalMsg_ (qc : QuorumCert) (pm : ProposalMsg) : Set where
     inProposal       : pm ^∙ pmProposal ∙ bBlockData ∙ bdQuorumCert ≡ qc → qc QC∈ProposalMsg pm
     inPMSIHighQC     : pm ^∙ pmSyncInfo ∙ siHighestQuorumCert ≡ qc       → qc QC∈ProposalMsg pm
     inPMSIHighCC     : pm ^∙ pmSyncInfo ∙ siHighestCommitCert ≡ qc       → qc QC∈ProposalMsg pm

  data _QC∈VoteMsg_ (qc : QuorumCert) (vm : VoteMsg) : Set where
     withVoteSIHighQC : vm ^∙ vmSyncInfo ∙ siHighestQuorumCert ≡ qc       → qc QC∈VoteMsg vm
     withVoteSIHighCC : vm ^∙ vmSyncInfo ∙ siHighestCommitCert ≡ qc       → qc QC∈VoteMsg vm

  data _QC∈CommitMsg_ (qc : QuorumCert) (cm : CommitMsg) : Set where
     withCommitMsg    : cm ^∙ cCert ≡ qc                                  → qc QC∈CommitMsg cm

  data _QC∈NM_ (qc : QuorumCert) : NetworkMsg → Set where
    inP : ∀ {pm} → qc QC∈ProposalMsg pm → qc QC∈NM (P pm)
    inV : ∀ {vm} → qc QC∈VoteMsg     vm → qc QC∈NM (V vm)
    inC : ∀ {cm} → qc QC∈CommitMsg   cm → qc QC∈NM (C cm)

  data _⊂Msg_ (v : Vote) : NetworkMsg → Set where
    vote∈vm : ∀ {si}
            → v ⊂Msg (V (VoteMsg∙new v si))
    vote∈qc : ∀ {vs} {qc : QuorumCert} {nm}
            → vs ∈ qcVotes qc
            → rebuildVote qc vs ≈Vote v
            → qc QC∈NM nm
            → v ⊂Msg nm

  getEpoch : NetworkMsg → EpochId
  getEpoch (P p) = p ^∙ pmProposal ∙ bBlockData ∙ bdEpoch
  getEpoch (V (VoteMsg∙new v _)) = v ^∙ vEpoch
  getEpoch (C c) = c ^∙ cEpochId

  -- Get the message's author, if it has one.  Note that ProposalMsgs don't necessarily have
  -- authors; we care about the (honesty of) the author only for Proposals, not NilBlocks and
  -- Genesis.
  getAuthor : NetworkMsg → Maybe NodeId
  getAuthor (P p)
     with p ^∙ pmProposal ∙ bBlockData ∙ bdBlockType
  ...| Proposal _ auth = just auth
  ...| NilBlock        = nothing
  ...| Genesis         = nothing
  getAuthor (V v) = just (v ^∙ vmVote ∙ vAuthor)
  getAuthor (C c) = just (c ^∙ cAuthor)

  -----------------------------------------------------------------------
  -- Proof that network records are signable and may carry a signature --
  -----------------------------------------------------------------------

  Signed-pi-CommitMsg : (c : CommitMsg)
                      → (is1 is2 : (Is-just ∘ ₋cSigMB) c)
                      → is1 ≡ is2
  Signed-pi-CommitMsg (CommitMsg∙new _ _ _ _ .(just _)) (just _) (just _) = cong just refl

  instance
   -- A proposal message might carry a signature inside the block it
   -- is proposing.
   sig-ProposalMsg : WithSig ProposalMsg
   sig-ProposalMsg = record
      { Signed         = Signed         ∘ ₋pmProposal
      ; Signed-pi      = Signed-pi-Blk  ∘ ₋pmProposal
      ; isSigned?      = isSigned?      ∘ ₋pmProposal
      ; signature      = signature      ∘ ₋pmProposal
      ; signableFields = signableFields ∘ ₋pmProposal
      }

   sig-VoteMsg : WithSig VoteMsg
   sig-VoteMsg = record
      { Signed         = Signed         ∘ ₋vmVote
      ; Signed-pi      = λ _ _ _ → Unit-pi
      ; isSigned?      = isSigned?      ∘ ₋vmVote
      ; signature      = signature      ∘ ₋vmVote
      ; signableFields = signableFields ∘ ₋vmVote
      }

   sig-CommitMsg : WithSig CommitMsg
   sig-CommitMsg = record
      { Signed         = Is-just ∘ ₋cSigMB
      ; Signed-pi      = Signed-pi-CommitMsg
      ; isSigned?      = λ c → Maybe-Any-dec (λ _ → yes tt) (c ^∙ cSigMB)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ c → concat ( encode  (c ^∙ cEpochId)
                                      ∷ encode  (c ^∙ cAuthor)
                                      ∷ encode  (c ^∙ cRound)
                                      ∷ encode  (c ^∙ cCert)
                                      ∷ [])
      }

  ---------------------------------------------------------
  -- Network Records whose signatures have been verified --
  ---------------------------------------------------------

  -- First we have to have some boilerplate to pattern match
  -- on the type of message to access the 'WithSig' instance
  -- on the fields... a bit ugly, but there's no other way, really.
  -- At least we quarantine them in a private block.
  private
    SignedNM : NetworkMsg → Set
    SignedNM (P x) = Signed x
    SignedNM (V x) = Signed x
    SignedNM (C x) = Signed x

    SignedNM-pi : ∀ (nm : NetworkMsg) → (is1 : SignedNM nm) → (is2 : SignedNM nm) → is1 ≡ is2
    SignedNM-pi (P x) = Signed-pi x
    SignedNM-pi (V x) = Signed-pi x
    SignedNM-pi (C x) = Signed-pi x

    isSignedNM? : (nm : NetworkMsg) → Dec (SignedNM nm)
    isSignedNM? (P x) = isSigned? x
    isSignedNM? (V x) = isSigned? x
    isSignedNM? (C x) = isSigned? x

    signatureNM  : (nm : NetworkMsg) → SignedNM nm → Signature
    signatureNM (P x) prf = signature x prf
    signatureNM (V x) prf = signature x prf
    signatureNM (C x) prf = signature x prf

    signableFieldsNM : NetworkMsg → ByteString
    signableFieldsNM (P x) = signableFields x
    signableFieldsNM (V x) = signableFields x
    signableFieldsNM (C x) = signableFields x

  instance
    sig-NetworkMsg : WithSig NetworkMsg
    sig-NetworkMsg = record
      { Signed         = SignedNM
      ; Signed-pi      = SignedNM-pi
      ; isSigned?      = isSignedNM?
      ; signature      = signatureNM
      ; signableFields = signableFieldsNM
      }
