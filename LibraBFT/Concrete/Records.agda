{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types using (isAuthor)
open import LibraBFT.Base.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import LibraBFT.Concrete.Consensus.Types

module LibraBFT.Concrete.Records where

  data NetworkMsg (A : Set) : Set where
    P : ProposalMsg A → NetworkMsg A
    V : VoteMsg       → NetworkMsg A
    C : CommitMsg     → NetworkMsg A

  -----------------------------------------------------------------------
  -- Proof that network records are signable and may carry a signature --
  -----------------------------------------------------------------------

  instance 
   -- A Block might carry a signature
   sig-Block : {A : Set} ⦃ encA : Encoder A ⦄ → WithSig (Block A)
   sig-Block = record
      { Signed         = Is-just ∘ bSignature 
      ; isSigned?      = λ b → Maybe-Any-dec (λ _ → yes tt) (bSignature b)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ b → concat (encodeH (bId b) ∷ encode (bBlockData b) ∷ []) 
      }
  
   -- A proposal message might carry a signature inside the block it
   -- is proposing.
   sig-ProposalMsg : {A : Set} ⦃ encA : Encoder A ⦄ → WithSig (ProposalMsg A)
   sig-ProposalMsg = record
      { Signed         = Signed         ∘ pmProposal 
      ; isSigned?      = isSigned?      ∘ pmProposal
      ; signature      = signature      ∘ pmProposal 
      ; signableFields = signableFields ∘ pmProposal 
      }

   -- A vote is always signed; as seen by the 'Unit'
   -- on the definition of Signed.
   -- VCM-QUESTION: What are the signable fields? What do we
   -- do with timeoutSignature?
   sig-Vote : WithSig Vote
   sig-Vote = record 
      { Signed         = λ _ → Unit 
      ; isSigned?      = λ _ → yes unit
      ; signature      = λ v _ → vSignature v 
      ; signableFields = λ v → concat {!!} 
      }

   sig-VoteMsg : WithSig VoteMsg
   sig-VoteMsg = record
      { Signed         = Signed         ∘ vmVote
      ; isSigned?      = isSigned?      ∘ vmVote
      ; signature      = signature      ∘ vmVote
      ; signableFields = signableFields ∘ vmVote
      }

   sig-commit : WithSig CommitMsg
   sig-commit = record
      { Signed         = Is-just ∘ cSigMB 
      ; isSigned?      = λ c → Maybe-Any-dec (λ _ → yes tt) (cSigMB c)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ c → concat ( encode  (cEpochId c) 
                                      ∷ encode  (cAuthor c) 
                                      ∷ encode  (cRound c) 
                                      ∷ encodeH (cCert c) 
                                      ∷ []) 
      }

  ---------------------------------------------------------
  -- Network Records whose signatures have been verified --
  ---------------------------------------------------------

  -- First we have to have some boilerplate to pattern match
  -- on the type of message to access the 'WithSig' instance
  -- on the fields... a bit ugly, but there's no other way, really...
  private
    SignedNM : {A : Set} ⦃ encA : Encoder A ⦄ → NetworkMsg A → Set
    SignedNM (P x) = Signed x
    SignedNM (V x) = Signed x
    SignedNM (C x) = Signed x

    isSignedNM? : {A : Set} ⦃ encA : Encoder A ⦄ → (nm : NetworkMsg A)
                → Dec (SignedNM nm)
    isSignedNM? (P x) = isSigned? x
    isSignedNM? (V x) = isSigned? x
    isSignedNM? (C x) = isSigned? x

    signatureNM  : {A : Set} ⦃ encA : Encoder A ⦄ → (nm : NetworkMsg A)
                 → SignedNM nm → Signature
    signatureNM (P x) prf = signature x prf
    signatureNM (V x) prf = signature x prf
    signatureNM (C x) prf = signature x prf

    signableFieldsNM : {A : Set} ⦃ encA : Encoder A ⦄ → (nm : NetworkMsg A)
                     → ByteString
    signableFieldsNM (P x) = signableFields x
    signableFieldsNM (V x) = signableFields x
    signableFieldsNM (C x) = signableFields x

  -- Finally, we hide those ugly auxiliar functions away in a 'private' block
  -- in favor of a neat instance:
  instance
    sig-NetworkMsg : {A : Set} ⦃ encA : Encoder A ⦄ → WithSig (NetworkMsg A)
    sig-NetworkMsg = record
      { Signed         = SignedNM
      ; isSigned?      = isSignedNM?
      ; signature      = signatureNM
      ; signableFields = signableFieldsNM
      }

  -- Now, we can have a more concise type of verified messages; 
  -- I think I prefer the old version, though... not sure
  VerNetworkMsg : (A : Set) ⦃ encA : Encoder A ⦄ → Set
  VerNetworkMsg A = Σ (NetworkMsg A) WithVerSig


  postulate  -- TODO implement
    check-signature-and-format : {a : Set} → ⦃ encA : Encoder a ⦄ → NetworkMsg a → Maybe (VerNetworkMsg a)

{-
  -- VCM: TODO: need to make sure messages were verified
  --            with the proper public key, no?
  -- MSM: Yes, but it's not clear to me if it should be done here.
  --      See the example use in ModelDraft.agda, where this check
  --      is done externally to VerNetworkMsg.  I think it probably
  --      makes sense to keep VerNetworkMsg independent of where
  --      public keys come from, but I don't feel strongly
  --      about it, so you can factor it in here if you think that's best.

-}

  
