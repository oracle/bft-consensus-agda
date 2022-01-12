{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.Verifier        as Verifier
open import LibraBFT.ImplShared.Consensus.Types
open import Optics.All
open import Util.Encode
open import Util.PKCS                           hiding (verify)
open import Util.Prelude
------------------------------------------------------------------------------
import      Data.List.Base                      as List
open import Data.String                         using (String)

module LibraBFT.Impl.Types.EpochChangeProof where

obmLastLIWS : EpochChangeProof → Either ErrLog LedgerInfoWithSignatures
obmLastLIWS self = maybeS (lastMay (self ^∙ ecpLedgerInfoWithSigs))
                          (Left fakeErr {-["EpochChangeProof", "obmLastLIWS", "empty"]-})
                          pure

-- first/lowest epoch of the proof to indicate which epoch this proof is helping with
epoch : EpochChangeProof -> Either ErrLog Epoch
epoch self = maybeS (headMay (self ^∙ ecpLedgerInfoWithSigs))
                    (Left fakeErr {-["EpochChangeProof", "epoch", "empty"]-})
                    (pure ∘ (_^∙ liwsLedgerInfo ∙ liEpoch))

obmLastEpoch : EpochChangeProof → Epoch
obmLastEpoch self = eitherS (obmLastLIWS self) (const ({-Epoch-} 0)) (_^∙ liwsLedgerInfo ∙ liEpoch)

verify
  : {verifier : Set} ⦃ _ : Verifier.Verifier verifier ⦄
  → EpochChangeProof → verifier
  → Either ErrLog LedgerInfoWithSignatures
verify self verifier = do
  lcheck (not (null (self ^∙ ecpLedgerInfoWithSigs)))
         (here' ("empty" ∷ []))
  lastLedgerInfoWithSigs ← last (self ^∙ ecpLedgerInfoWithSigs)
  lcheckInfo (not (Verifier.isLedgerInfoStale verifier (lastLedgerInfoWithSigs ^∙ liwsLedgerInfo)))
             (here' ("stale" ∷ []))
      -- Skip stale ledger infos in the proof prefix.
  let ledgerInfosWithSigs =
        List.boolFilter
          (λ liws → not (Verifier.isLedgerInfoStale verifier (liws ^∙ liwsLedgerInfo)))
          (self ^∙ ecpLedgerInfoWithSigs)

  -- check the non-stale chain
  loop verifier ledgerInfosWithSigs

  pure lastLedgerInfoWithSigs
 where
  loop
    : {verifier : Set} ⦃ _ : Verifier.Verifier verifier ⦄
    → verifier → List LedgerInfoWithSignatures
    → Either ErrLog Unit
  loop verifierRef = λ where
    [] → pure unit
    (liws ∷ liwss) → do
      Verifier.verify verifierRef liws
      verifierRef' ← case liws ^∙ liwsLedgerInfo ∙ liNextEpochState of λ where
        nothing   → Left fakeErr -- ["empty ValidatorSet"]
        (just vs) → pure vs
      loop verifierRef' liwss

  here' : List String → List String
  here' t = "EpochChangeProof" ∷ "verify" ∷ t

  last : ∀ {A : Set} → List A → Either ErrLog A
  last          []  = Left fakeErr
  last     (x ∷ []) = Right x
  last (_ ∷ x ∷ xs) = last xs
