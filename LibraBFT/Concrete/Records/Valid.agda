{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import LibraBFT.Concrete.Util.KVMap
open import LibraBFT.Concrete.Consensus.Types

import LibraBFT.Abstract.Types as Abs

-- Proofs for validity of concrete records
module LibraBFT.Concrete.Records.Valid 
    (ec  : Abs.EpochConfig)
    (pki : PKI)
  where

 open import LibraBFT.Concrete.Records

 record IsValidQCAuthor (_ : Author) : Set where
   field
     ivaIdx : Abs.Author ec
 open IsValidQCAuthor public

 record IsValidQC (qc : QuorumCert) : Set where
   field
     ivqcSizeOk       : Abs.QuorumSize ec ≤ length (qcVotes qc)
     ivqcValidAuthors : All (IsValidQCAuthor ∘ proj₁) (qcVotes qc)
 open IsValidQC public
   
     -- TODO: Add fields as we need them

 validateQC : (qc : QuorumCert) → Maybe (IsValidQC qc)
 validateQC = {!!}
            

  

