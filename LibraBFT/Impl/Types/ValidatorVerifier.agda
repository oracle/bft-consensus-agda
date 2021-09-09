{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Base.KVMap                            as Map
open import LibraBFT.Base.PKCS                             hiding (verify)
import      LibraBFT.Impl.OBM.Crypto                       as Crypto
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.Impl.OBM.Util
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
open import Data.String                                    using (String)

module LibraBFT.Impl.Types.ValidatorVerifier where

------------------------------------------------------------------------------
calculateQuorumVotingPower : U64 -> U64
checkNumOfSignatures       : ValidatorVerifier → Map.KVMap AccountAddress Signature
                           → Either ErrLog Unit
checkVotingPower           : ValidatorVerifier → List AccountAddress → Either ErrLog Unit
getPublicKey               : ValidatorVerifier → AccountAddress → Maybe PK
getVotingPower             : ValidatorVerifier → AccountAddress → Maybe U64
sumVotingPower             : (List String → List String)
                           → Map.KVMap AccountAddress ValidatorConsensusInfo
                           → Either ErrLog U64
------------------------------------------------------------------------------

-- LBFT-OBM-DIFF : this is specific to OBM.
-- It enables specifying the number of faults allowed.
-- Assumes everyone has 1 vote
-- IMPL-DIFF : gets an alist instead of list of Author
initValidatorVerifier
  : U64 → List (Author × (SK × PK))
  → Either ErrLog ValidatorVerifier
initValidatorVerifier numFailures0 authors0 =
  checkBftAndRun numFailures0 authors0 f
 where
  f : U64 → List (Author × (SK × PK)) → ValidatorVerifier
  f numFailures authors =
    record -- ValidatorVerifier
    { _vvAddressToValidatorInfo = Map.fromList (fmap (λ (author , (_ , pk)) →
                                                       (author , ValidatorConsensusInfo∙new pk 1))
                                                    authors)
    ; _vvQuorumVotingPower      = numNodesNeededForNFailures numFailures ∸ numFailures
    ; _vvTotalVotingPower       = length authors }

new : Map.KVMap AccountAddress ValidatorConsensusInfo → Either ErrLog ValidatorVerifier
new addressToValidatorInfo = do
  totalVotingPower      ← sumVotingPower here' addressToValidatorInfo
  let quorumVotingPower = if Map.kvm-size addressToValidatorInfo == 0 then 0
                          else calculateQuorumVotingPower totalVotingPower
  pure (mkValidatorVerifier addressToValidatorInfo quorumVotingPower totalVotingPower)
 where
  here' : List String → List String
  here' t = "ValidatorVerifier" ∷ "new" ∷ t

-- This scales up the number of faults tolerated with the number of votes.
-- see TestValidatorVerifier in Haskell
calculateQuorumVotingPower totalVotingPower = (div (totalVotingPower * 2) 3) + 1

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
  → ValidatorVerifier → V → Map.KVMap AccountAddress Signature
  → Either ErrLog Unit
verifyAggregatedStructSignature self v aggregatedSignature = do
  checkNumOfSignatures self aggregatedSignature
  checkVotingPower self (Map.kvm-keys aggregatedSignature)
  forM_ (Map.kvm-toList aggregatedSignature) λ (author , signature) →
    verify self author v signature

batchVerifyAggregatedSignatures
  : {V : Set} ⦃ _ : Crypto.CryptoHash V ⦄
  → ValidatorVerifier → V → Map.KVMap AccountAddress Signature
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
  (_^∙ vciPublicKey)   <$> Map.lookup author (self ^∙ vvAddressToValidatorInfo)

getVotingPower self author =
  (_^∙ vciVotingPower) <$> Map.lookup author (self ^∙ vvAddressToValidatorInfo)

sumVotingPower here' addressToValidatorInfo =
  foldr go (Right 0) (Map.elems addressToValidatorInfo)
 where
  maxBoundU64 : U64
  maxBoundU64 = 18446744073709551615
  go : ValidatorConsensusInfo → Either ErrLog U64 → Either ErrLog U64
  go x (Right sum') =
    if-dec sum' ≤? maxBoundU64 ∸ (x ^∙ vciVotingPower)
    then Right (sum' + x ^∙ vciVotingPower)
    else Left fakeErr -- (ErrL (here' ("sum too big" ∷ [])))
  go _ (Left err) = Left err

getOrderedAccountAddressesObmTODO : ValidatorVerifier → List AccountAddress
getOrderedAccountAddressesObmTODO self =
  -- TODO ORDER
  Map.kvm-keys (self ^∙ vvAddressToValidatorInfo)

from : ValidatorSet → Either ErrLog ValidatorVerifier
from validatorSet =
  new (foldl' go Map.empty (validatorSet ^∙ vsPayload))
 where
  go : Map.KVMap AccountAddress ValidatorConsensusInfo → ValidatorInfo
     → Map.KVMap AccountAddress ValidatorConsensusInfo
  go map0 validator =
    Map.insert (validator ^∙ viAccountAddress)
               (ValidatorConsensusInfo∙new
                 (validator ^∙ viConsensusPublicKey)
                 (validator ^∙ viConsensusVotingPower))
                map0
