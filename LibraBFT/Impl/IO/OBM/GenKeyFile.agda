{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
import      LibraBFT.Impl.OBM.Genesis                      as Genesis
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.Impl.OBM.Util
import      LibraBFT.Impl.Types.OnChainConfig.ValidatorSet as ValidatorSet
import      LibraBFT.Impl.Types.ValidatorVerifier          as ValidatorVerifier
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

module LibraBFT.Impl.IO.OBM.GenKeyFile where

------------------------------------------------------------------------------

EndpointAddress           = Author
AddressToSkAndPkAssocList = List (EndpointAddress × (SK × PK))

------------------------------------------------------------------------------
genKeys   : {-Crypto.SystemDRG →-} ℕ   → List (SK × PK)
mkAuthors : {-Crypto.SystemDRG →-} U64 → List EndpointAddress
          → Either ErrLog AddressToSkAndPkAssocList
mkValidatorSignersAndVerifierAndProposerElection
          : U64 → AddressToSkAndPkAssocList
          → Either ErrLog (List ValidatorSigner × ValidatorVerifier × ProposerElection)
------------------------------------------------------------------------------

NfLiwsVssVvPe =
  (U64 × LedgerInfoWithSignatures × List ValidatorSigner × ValidatorVerifier × ProposerElection)

create'
  : U64 → List EndpointAddress {-→ SystemDRG-}
  → Either ErrLog
    ( U64 × AddressToSkAndPkAssocList
    × List ValidatorSigner × ValidatorVerifier × ProposerElection × LedgerInfoWithSignatures )
create' numFailures addresses {-drg-} = do
 authors       ← mkAuthors {-drg-} numFailures addresses
 (s , vv , pe) ← mkValidatorSignersAndVerifierAndProposerElection numFailures authors
 case Genesis.obmMkGenesisLedgerInfoWithSignatures s (ValidatorSet.obmFromVV vv) of λ where
       (Left err)   → Left err
       (Right liws) → pure (numFailures , authors , s , vv , pe , liws)

abstract
  create = create'
  create≡ : create ≡ create'
  create≡ = refl

mkAuthors {-drg-} numFailures0 addresses0 = do
  addrs <- checkAddresses
  checkBftAndRun numFailures0 addrs f
 where
  f : ℕ → List EndpointAddress → AddressToSkAndPkAssocList
  f _numFailures addresses = zip addresses (genKeys {-drg-} (length addresses))
  checkAddresses : Either ErrLog (List EndpointAddress)
  checkAddresses = pure addresses0

postulate
  mkSK : NodeId → SK
  mkPK : NodeId → PK

genKeys    zero   = []
genKeys x@(suc n) = (mkSK x , mkPK x) ∷ genKeys n

mkValidatorSignersAndVerifierAndProposerElection numFaults ks = do
  -- IMPL-DIFF: Agda Author type does NOT contain a PK
  let allAuthors       = fmap fst ks
  validatorVerifier    ← ValidatorVerifier.initValidatorVerifier numFaults ks
  let authorKeyPairs   = fmap (λ (a , (sk , _)) → (a , sk)) ks
      validatorSigners = foldl' go [] authorKeyPairs
  pure (validatorSigners , validatorVerifier , ProposerElection∙new allAuthors)
 where
  go : List ValidatorSigner → (Author × SK) → List ValidatorSigner
  go acc (author , sk) = ValidatorSigner∙new author sk ∷ acc
