{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap                            as Map
open import LibraBFT.Base.PKCS                             hiding (verify)
import      LibraBFT.Impl.OBM.Crypto                       as Crypto
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Types.ValidatorVerifier where

checkNumOfSignatures : ValidatorVerifier → KVMap AccountAddress Signature → Either ErrLog Unit
checkVotingPower     : ValidatorVerifier → List AccountAddress → Either ErrLog Unit
getPublicKey         : ValidatorVerifier → AccountAddress → Maybe PK
getVotingPower       : ValidatorVerifier → AccountAddress → Maybe U64

verifyIfAuthor
  : {V : Set} ⦃ _ : Crypto.CryptoHash V ⦄
  → {-Text →-} ValidatorVerifier → AccountAddress → V → Signature
  → Either ErrLog Unit
verifyIfAuthor {-msg-} self author v signature = case getPublicKey self author of λ where
  (just pk) → case Crypto.verify {-msg-} pk signature v of λ where
                (Left  e)    → Left fakeErr -- (ErrVerify e InvalidSignature)
                (Right unit) → Right unit
  nothing  → Left fakeErr -- Left (ErrVerify (msg:known) (UnknownAuthor (author^.aAuthorName)))
-- where
--  known = fmap _aAuthorName (Map.keys (self^.vvAddressToValidatorInfo))

verify
  : {V : Set} ⦃ _ : Crypto.CryptoHash V ⦄
  → ValidatorVerifier → AccountAddress → V → Signature
  → Either ErrLog Unit
verify = verifyIfAuthor -- (icSemi ["ValidatorVerifier", "verifySignature"])

verifyAggregatedStructSignature
  : {V : Set} ⦃ _ : Crypto.CryptoHash V ⦄
  → ValidatorVerifier → V → KVMap AccountAddress Signature
  → Either ErrLog Unit
verifyAggregatedStructSignature self v aggregatedSignature = do
  checkNumOfSignatures self aggregatedSignature
  checkVotingPower self (Map.kvm-keys aggregatedSignature)
  forM_ (Map.kvm-toList aggregatedSignature) λ (author , signature) →
    verify self author v signature

batchVerifyAggregatedSignatures
  : {V : Set} ⦃ _ : Crypto.CryptoHash V ⦄
  → ValidatorVerifier → V → KVMap AccountAddress Signature
  → Either ErrLog Unit
batchVerifyAggregatedSignatures = verifyAggregatedStructSignature

checkNumOfSignatures self aggregatedSignature =
  if-dec Map.kvm-size aggregatedSignature >? Map.kvm-size (self ^∙ vvAddressToValidatorInfo)
    then Left (ErrVerify
                 (TooManySignatures
                   (Map.kvm-size aggregatedSignature)
                   (Map.kvm-size (self ^∙ vvAddressToValidatorInfo))))
    else Right unit

checkVotingPower self authors = do
  let go : AccountAddress → U64 → Either ErrLog U64
      go a acc = case getVotingPower self a of λ where
         nothing  → Left (ErrVerify (UnknownAuthor (a ^∙ aAuthorName)))
         (just n) → Right (n + acc)
  aggregatedVotingPower ← foldrM go 0 authors
  if-dec aggregatedVotingPower <? self ^∙ vvQuorumVotingPower
    then Left (ErrVerify
               (TooLittleVotingPower aggregatedVotingPower (self ^∙ vvQuorumVotingPower)))
    else Right unit

getPublicKey self author =
  (_^∙ vciPublicKey) <$> Map.lookup author (self ^∙ vvAddressToValidatorInfo)

getVotingPower self author =
  (_^∙ vciVotingPower) <$> Map.lookup author (self ^∙ vvAddressToValidatorInfo)
