{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.KVMap                            as Map
open import LibraBFT.Base.PKCS                             hiding (verify)
import      LibraBFT.Impl.OBM.Crypto                       as Crypto
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.Types.ValidatorVerifier where

checkNumOfSignatures : ValidatorVerifier → KVMap AccountAddress Signature → Either FakeErr Unit
checkVotingPower     : ValidatorVerifier → List AccountAddress → Either FakeErr Unit
getPublicKey         : ValidatorVerifier → AccountAddress → Maybe PK
getVotingPower       : ValidatorVerifier → AccountAddress → Maybe U64

verifyIfAuthor
  : {V : Set} ⦃ _ : Crypto.CryptoHash V ⦄
  → {-Text →-} ValidatorVerifier → AccountAddress → V → Signature
  → Either FakeErr Unit
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
  → Either FakeErr Unit
verify = verifyIfAuthor -- (icSemi ["ValidatorVerifier", "verifySignature"])

verifyAggregatedStructSignature
  : {V : Set} ⦃ _ : Crypto.CryptoHash V ⦄
  → ValidatorVerifier → V → KVMap AccountAddress Signature
  → Either FakeErr Unit
verifyAggregatedStructSignature self v aggregatedSignature = do
  checkNumOfSignatures self aggregatedSignature
  checkVotingPower self (Map.kvm-keys aggregatedSignature)
  loop (Map.kvm-toList aggregatedSignature)
 where
  loop : List (Author × Signature) → Either FakeErr Unit
  loop  []  = Right unit
  loop ((author , signature) ∷ xs) =
    case verify self author v signature of λ where
      (Right unit) → loop xs
      l            → l

batchVerifyAggregatedSignatures
  : {V : Set} ⦃ _ : Crypto.CryptoHash V ⦄
  → ValidatorVerifier → V → KVMap AccountAddress Signature
  → Either FakeErr Unit
batchVerifyAggregatedSignatures = verifyAggregatedStructSignature

checkNumOfSignatures self aggregatedSignature =
  if-dec Map.kvm-size aggregatedSignature >? Map.kvm-size (self ^∙ vvAddressToValidatorInfo)
    then Left fakeErr -- ErrVerify TooManySignatures (Map.size aggregatedSignature)
                      -- (Map.size (self^.vvAddressToValidatorInfo)
    else Right unit

checkVotingPower self authors = loop authors 0
 where
  loop : List AccountAddress → U64 → Either FakeErr Unit
  loop (a ∷ as) acc = case getVotingPower self a of λ where
                        nothing  → Left (ErrVerify (UnknownAuthor (a ^∙ aAuthorName)))
                        (just n) → loop as (n + acc)
  loop [] aggregatedVotingPower =
    if-dec aggregatedVotingPower <? self ^∙ vvQuorumVotingPower
    then Left (ErrVerify (TooLittleVotingPower aggregatedVotingPower (self ^∙ vvQuorumVotingPower)))
    else Right unit

getPublicKey self author =
--  (^.vciPublicKey) <$> Map.lookup author (self^.vvAddressToValidatorInfo)
  case Map.lookup author (self ^∙ vvAddressToValidatorInfo) of λ where
    nothing  → nothing
    (just a) → just (a ^∙ vciPublicKey)

getVotingPower self author =
--  (λ a → a ^∙ vciVotingPower) <$> (Map.lookup author (self ^∙ vvAddressToValidatorInfo))
  case Map.lookup author (self ^∙ vvAddressToValidatorInfo) of λ where
    nothing  → nothing
    (just a) → just (a ^∙ vciVotingPower)

