{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Util.Crypto
open import Optics.All
open import Util.ByteString
open import Util.Encode
open import Util.Hash
open import Util.Lemmas
open import Util.PKCS
open import Util.Prelude
open import Util.Types

-- This module defines the types of messages that the implementation
-- can send, along with properties defining ways in which votes can be
-- represented in them, some useful functions, and definitions of how
-- NetworkMsgs are signed.

module LibraBFT.ImplShared.NetworkMsg where
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

  data _QC∈SyncInfo_ (qc : QuorumCert) (si : SyncInfo) : Set where
     withVoteSIHighQC : si ^∙ siHighestQuorumCert  ≡ qc   → qc QC∈SyncInfo si
     -- Note that we do not use the Lens here, because the Lens returns the siHighestQuorumcert in
     -- case siHighestCommitcert is nothing, and it was easier to directly handle the just case.  We
     -- could use the Lens, and fix the proofs, but it seems simpler this way.
     withVoteSIHighCC : _sixxxHighestCommitCert si ≡ just qc → qc QC∈SyncInfo si

  data _SyncInfo∈NM_ : SyncInfo → NetworkMsg → Set where
    inP  : ∀ {pm} → (pm ^∙ pmSyncInfo) SyncInfo∈NM P pm
    inV  : ∀ {vm} → (vm ^∙ vmSyncInfo) SyncInfo∈NM V vm

  data _QC∈NM_ : QuorumCert → NetworkMsg → Set where
    inP  : ∀ {pm}       → (pm ^∙ pmProposal ∙ bBlockData ∙ bdQuorumCert) QC∈NM (P pm)
    inSI : ∀ {nm si qc} → si SyncInfo∈NM nm → qc QC∈SyncInfo si → qc     QC∈NM nm
    inC  : ∀ {cm}       → (cm ^∙ cmCert)                                 QC∈NM (C cm)

  data _⊂Msg_ (v : Vote) : NetworkMsg → Set where
    vote∈vm : ∀ {si}
            → v ⊂Msg (V (VoteMsg∙new v si))
    vote∈qc : ∀ {vs} {qc : QuorumCert} {nm}
            → vs ∈ qcVotes qc
            → rebuildVote qc vs ≈Vote v
            → qc QC∈NM nm
            → v ⊂Msg nm

  data _Block∈Msg_ (b : Block) : NetworkMsg → Set where
    inP : ∀ {pm} → pm ^∙ pmProposal ≡ b → b Block∈Msg (P pm)

  getEpoch : NetworkMsg → Epoch
  getEpoch (P p) = p ^∙ pmProposal ∙ bBlockData ∙ bdEpoch
  getEpoch (V (VoteMsg∙new v _)) = v ^∙ vEpoch
  getEpoch (C c) = c ^∙ cmEpoch

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

  -----------------------------------------------------------------------
  -- Proof that network records are signable and may carry a signature --
  -----------------------------------------------------------------------

  Signed-pi-CommitMsg : (cm : CommitMsg)
                      → (is1 is2 : (Is-just ∘ _cmSigMB) cm)
                      → is1 ≡ is2
  Signed-pi-CommitMsg (CommitMsg∙new _ _ _ _ .(just _)) (just _) (just _) = cong just refl

  instance
   -- A proposal message might carry a signature inside the block it
   -- is proposing.
   sig-ProposalMsg : WithSig ProposalMsg
   sig-ProposalMsg = record
      { Signed         = Signed         ∘ _pmProposal
      ; Signed-pi      = Signed-pi-Blk  ∘ _pmProposal
      ; isSigned?      = isSigned?      ∘ _pmProposal
      ; signature      = signature      ∘ _pmProposal
      ; signableFields = signableFields ∘ _pmProposal
      }

   sig-VoteMsg : WithSig VoteMsg
   sig-VoteMsg = record
      { Signed         = Signed         ∘ _vmVote
      ; Signed-pi      = λ _ _ _ → Unit-pi
      ; isSigned?      = isSigned?      ∘ _vmVote
      ; signature      = signature      ∘ _vmVote
      ; signableFields = signableFields ∘ _vmVote
      }

   sig-CommitMsg : WithSig CommitMsg
   sig-CommitMsg = record
      { Signed         = Is-just ∘ _cmSigMB
      ; Signed-pi      = Signed-pi-CommitMsg
      ; isSigned?      = λ cm → Maybe-Any-dec (λ _ → yes tt) (cm ^∙ cmSigMB)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ cm → concat ( encode  (cm ^∙ cmEpoch)
                                       ∷ encode  (cm ^∙ cmAuthor)
                                       ∷ encode  (cm ^∙ cmRound)
                                       ∷ encode  (cm ^∙ cmCert)
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
