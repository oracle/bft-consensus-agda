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
    G : GenesisMsg  → NetworkMsg

  P≢V : ∀ {p v} → P p ≢ V v
  P≢V ()

  C≢V : ∀ {c v} → C c ≢ V v
  C≢V ()

  G≢V : ∀ {g v} → G g ≢ V v
  G≢V ()

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
     withCommitMsg    : cm ^∙ cmCert ≡ qc                                 → qc QC∈CommitMsg cm

  data _QC∈GenesisMsg_ (qc : QuorumCert) (gm : GenesisMsg) : Set where
     withGenesisMsg   : ₋genQC (₋gmGenInfo gm) ≡ qc                       → qc QC∈GenesisMsg gm

  data _QC∈NM_ (qc : QuorumCert) : NetworkMsg → Set where
    inP : ∀ {pm} → qc QC∈ProposalMsg pm → qc QC∈NM (P pm)
    inV : ∀ {vm} → qc QC∈VoteMsg     vm → qc QC∈NM (V vm)
    inC : ∀ {cm} → qc QC∈CommitMsg   cm → qc QC∈NM (C cm)
    inG : ∀ {gm} → qc QC∈GenesisMsg  gm → qc QC∈NM (G gm)

  data _⊂Msg_ (v : Vote) : NetworkMsg → Set where
    vote∈vm : ∀ {si}
            → v ⊂Msg (V (VoteMsg∙new v si))
    vote∈qc : ∀ {vs} {qc : QuorumCert} {nm}
            → vs ∈ qcVotes qc
            → rebuildVote qc vs ≈Vote v
            → qc QC∈NM nm
            → v ⊂Msg nm

  getEpoch : NetworkMsg → Epoch
  getEpoch (P p) = p ^∙ pmProposal ∙ bBlockData ∙ bdEpoch
  getEpoch (V (VoteMsg∙new v _)) = v ^∙ vEpoch
  getEpoch (C c) = c ^∙ cmEpoch
  getEpoch (G g) = 1 -- Could take it from genesis info, but we'll be proving it's 1 anyway

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
  getAuthor (C c) = just (c ^∙ cmAuthor)
  getAuthor (G g) = nothing

  -----------------------------------------------------------------------
  -- Proof that network records are signable and may carry a signature --
  -----------------------------------------------------------------------

  Signed-pi-CommitMsg : (cm : CommitMsg)
                      → (is1 is2 : (Is-just ∘ ₋cmSigMB) cm)
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
      { Signed         = Is-just ∘ ₋cmSigMB
      ; Signed-pi      = Signed-pi-CommitMsg
      ; isSigned?      = λ cm → Maybe-Any-dec (λ _ → yes tt) (cm ^∙ cmSigMB)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ cm → concat ( encode  (cm ^∙ cmEpoch)
                                       ∷ encode  (cm ^∙ cmAuthor)
                                       ∷ encode  (cm ^∙ cmRound)
                                       ∷ encode  (cm ^∙ cmCert)
                                       ∷ [])
      }

   -- Genesis messages are not signed, the necessary signatures are represented in GenesisInfo
   sig-GenesisMsg : WithSig GenesisMsg
   sig-GenesisMsg = record
      { Signed         = const ⊥
      ; Signed-pi      = λ _ ()
      ; isSigned?      = λ gm → no id
      ; signature      = λ {_ ()}
      ; signableFields = λ cm → []
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
    SignedNM (G x) = Signed x

    SignedNM-pi : ∀ (nm : NetworkMsg) → (is1 : SignedNM nm) → (is2 : SignedNM nm) → is1 ≡ is2
    SignedNM-pi (P x) = Signed-pi x
    SignedNM-pi (V x) = Signed-pi x
    SignedNM-pi (C x) = Signed-pi x

    isSignedNM? : (nm : NetworkMsg) → Dec (SignedNM nm)
    isSignedNM? (P x) = isSigned? x
    isSignedNM? (V x) = isSigned? x
    isSignedNM? (C x) = isSigned? x
    isSignedNM? (G x) = isSigned? x

    signatureNM  : (nm : NetworkMsg) → SignedNM nm → Signature
    signatureNM (P x) prf = signature x prf
    signatureNM (V x) prf = signature x prf
    signatureNM (C x) prf = signature x prf

    signableFieldsNM : NetworkMsg → ByteString
    signableFieldsNM (P x) = signableFields x
    signableFieldsNM (V x) = signableFields x
    signableFieldsNM (C x) = signableFields x
    signableFieldsNM (G x) = signableFields x

  instance
    sig-NetworkMsg : WithSig NetworkMsg
    sig-NetworkMsg = record
      { Signed         = SignedNM
      ; Signed-pi      = SignedNM-pi
      ; isSigned?      = isSignedNM?
      ; signature      = signatureNM
      ; signableFields = signableFieldsNM
      }
