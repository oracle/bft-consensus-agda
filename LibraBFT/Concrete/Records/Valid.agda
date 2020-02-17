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
  where

 open import LibraBFT.Concrete.Records

 -- This will really be in the actual algorithm (model)
 validateQC : (qc : QuorumCert) → Maybe (IsValidQC ec qc)
 validateQC = {!!}

