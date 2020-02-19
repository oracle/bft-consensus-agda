{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types using (isAuthor)
open import LibraBFT.Base.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import Optics.All

open import LibraBFT.Concrete.Consensus.Types

-- VCM: We should rename this module to network records, no?
module LibraBFT.Concrete.Records where

  data NetworkMsg : Set where
    P : ProposalMsg → NetworkMsg
    V : VoteMsg     → NetworkMsg
    C : CommitMsg   → NetworkMsg

  getEpoch : NetworkMsg → EpochId
  getEpoch (P p) = p ^∙ pmProposal ∙ bBlockData ∙ bdEpoch
  getEpoch (V v) = v ^∙ vmVote ∙ vVoteData ∙ vdProposed ∙ biEpoch
  getEpoch (C c) = c ^∙ cEpochId

  -----------------------------------------------------------------------
  -- Proof that network records are signable and may carry a signature --
  -----------------------------------------------------------------------

  instance
   -- A Block might carry a signature
   sig-Block : WithSig Block
   sig-Block = record  
      { Signed         = Is-just ∘ _bSignature 
      ; isSigned?      = λ b → Maybe-Any-dec (λ _ → yes tt) (b ^∙ bSignature)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ b → concat (encodeH (_bId b) ∷ encode (b ^∙ bBlockData) ∷ [])
      }

   -- A proposal message might carry a signature inside the block it
   -- is proposing.
   sig-ProposalMsg : WithSig ProposalMsg
   sig-ProposalMsg = record
      { Signed         = Signed         ∘ _pmProposal
      ; isSigned?      = isSigned?      ∘ _pmProposal
      ; signature      = signature      ∘ _pmProposal
      ; signableFields = signableFields ∘ _pmProposal
      }

   -- A vote is always signed; as seen by the 'Unit'
   -- on the definition of Signed.
   -- VCM-QUESTION: What are the signable fields? What do we
   -- do with timeoutSignature?
   sig-Vote : WithSig Vote
   sig-Vote = record
      { Signed         = λ _ → Unit
      ; isSigned?      = λ _ → yes unit
      ; signature      = λ v _ → _vSignature v
      ; signableFields = λ v → concat {!!}
      }

   sig-VoteMsg : WithSig VoteMsg
   sig-VoteMsg = record
      { Signed         = Signed         ∘ _vmVote
      ; isSigned?      = isSigned?      ∘ _vmVote
      ; signature      = signature      ∘ _vmVote
      ; signableFields = signableFields ∘ _vmVote
      }

   sig-commit : WithSig CommitMsg
   sig-commit = record
      { Signed         = Is-just ∘ _cSigMB
      ; isSigned?      = λ c → Maybe-Any-dec (λ _ → yes tt) (c ^∙ cSigMB)
      ; signature      = λ { _ prf → to-witness prf }
      ; signableFields = λ c → concat ( encode  (c ^∙ cEpochId)
                                      ∷ encode  (c ^∙ cAuthor)
                                      ∷ encode  (c ^∙ cRound)
                                      ∷ encodeH (c ^∙ cCert)
                                      ∷ [])
      }

  ---------------------------------------------------------
  -- Network Records whose signatures have been verified --
  ---------------------------------------------------------

  -- First we have to have some boilerplate to pattern match
  -- on the type of message to access the 'WithSig' instance
  -- on the fields... a bit ugly, but there's no other way, really...
  private
    SignedNM : NetworkMsg → Set
    SignedNM (P x) = Signed x
    SignedNM (V x) = Signed x
    SignedNM (C x) = Signed x

    isSignedNM? : (nm : NetworkMsg)
                → Dec (SignedNM nm)
    isSignedNM? (P x) = isSigned? x
    isSignedNM? (V x) = isSigned? x
    isSignedNM? (C x) = isSigned? x

    signatureNM  : (nm : NetworkMsg)
                 → SignedNM nm → Signature
    signatureNM (P x) prf = signature x prf
    signatureNM (V x) prf = signature x prf
    signatureNM (C x) prf = signature x prf

    signableFieldsNM : NetworkMsg
                     → ByteString
    signableFieldsNM (P x) = signableFields x
    signableFieldsNM (V x) = signableFields x
    signableFieldsNM (C x) = signableFields x

  -- Finally, we hide those ugly auxiliar functions away in a 'private' block
  -- in favor of a neat instance:
  instance
    sig-NetworkMsg : WithSig NetworkMsg
    sig-NetworkMsg = record
      { Signed         = SignedNM
      ; isSigned?      = isSignedNM?
      ; signature      = signatureNM
      ; signableFields = signableFieldsNM
      }

  -- Now, we can have a more concise type of verified messages; 
  -- I think I prefer the old version, though... not sure
  VerNetworkMsg : (A : Set) ⦃ encA : Encoder A ⦄ → Set
  VerNetworkMsg A = Σ NetworkMsg WithVerSig


  postulate  -- TODO implement
    check-signature-and-format : {a : Set} → ⦃ encA : Encoder a ⦄ → NetworkMsg → Maybe (VerNetworkMsg a)

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

  
