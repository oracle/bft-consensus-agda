{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.PKCS
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.Impl.OBM.Util
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

module LibraBFT.Impl.IO.OBM.GenKeyFile where

EndpointAddress           = NodeId
AddressToSkAndPkAssocList = List (EndpointAddress × (SK × PK))

------------------------------------------------------------------------------
genKeys   : {-Crypto.SystemDRG →-} ℕ   → List (SK × PK)
mkAuthors : {-Crypto.SystemDRG →-} U64 → List EndpointAddress
          → Either ErrLog AddressToSkAndPkAssocList
-- mkValidatorSignersAndVerifierAndProposerElection
--           : U64 → AddressToSkAndAuthorAssocList
--           → (List ValidatorSigner × ValidatorVerifier × ProposerElection)
------------------------------------------------------------------------------

NfLiwsVssVvPe =
  (U64 × LedgerInfoWithSignatures × List ValidatorSigner × ValidatorVerifier × ProposerElection)

-- create
--   : U64 → List EndpointAddress {-→ SystemDRG-}
--   → Either ErrLog -- IMPL-DIFF : Haskell does errorExit
--     ( U64 × AddressToSkAndPkAssocList
--     × List ValidatorSigner × ValidatorVerifier × ProposerElection × LedgerInfoWithSignatures )
-- create numFailures addresses {-drg-} = do
--    let authors     = mkAuthors {-drg-} numFailures addresses
--    {!!}
--       (s ,vv ,pe) = mkValidatorSignersAndVerifierAndProposerElection
--                       numFailures
--                       (convertSkPkToSkAuthorAssocList authors)
--     -------------------------
--    in case Genesis.obmMkGenesisLedgerInfoWithSignatures s (ValidatorSet.obmFromVV vv) of
--         Left err   → errorExit (errText err)
--         Right liws → (numFailures , authors , s , vv , pe , liws)

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

-- mkValidatorSignersAndVerifierAndProposerElection numFaults ks =
--   let allAuthors          = fmap (snd . snd) ks
--       validatorVerifier   = ValidatorVerifier.initValidatorVerifier numFaults allAuthors
--       authorKeyPairs      = fmap (\(_, (sk, a)) → (a, sk)) ks
--       go acc (author, sk) = ValidatorSigner.new author sk : acc
--       validatorSigners    = foldl' go [] authorKeyPairs
--    in (validatorSigners, validatorVerifier, ProposerElection.new allAuthors)
