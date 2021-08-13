{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Base.KVMap                                   as Map
import      LibraBFT.Impl.Consensus.ConsensusTypes.BlockRetrieval as BlockRetrieval
import      LibraBFT.Impl.IO.OBM.ObmNeedFetch                     as ObmNeedFetch
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.OBM.Rust.RustTypes
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                                           as String

module LibraBFT.Impl.Consensus.BlockStorage.BlockRetriever where

pickPeer : ℕ → List Author → Either ErrLog (Author × List Author)

-- LBFT-OBM-DIFF : this lives in sync_manager.rs (in this file to isolate IO)
-- TODO-1 PROVE IT TERMINATES
{-# TERMINATING #-}
retrieveBlockForQCM : BlockRetriever → QuorumCert → U64 → LBFT (Either ErrLog (List Block))
retrieveBlockForQCM _retriever qc numBlocks =
  loop (qc ^∙ qcCertifiedBlock ∙ biId) 0 (Map.kvm-keys (qc ^∙ qcLedgerInfo ∙ liwsSignatures))
 where
  doLoop : HashValue → ℕ → List Author → LBFT (Either ErrLog (List Block))
  logIt  : InfoLog → LBFT Unit
  here'  : List String.String → List String.String

  loop : HashValue → ℕ → List Author → LBFT (Either ErrLog (List Block))
  loop blockId attempt = λ where
    [] → bail fakeErr -- [ "failed to fetch block, no more peers available"
                      -- , lsHV blockId, show attempt ]
    peers0@(_ ∷ _) → do
      mme               ← use (lRoundManager ∙ rmObmMe)
      maybeSD mme (bail fakeErr) $ λ me → do
        nf                ← use lObmNeedFetch
        eitherS (pickPeer attempt peers0) bail $ λ (peer , peers) → do
          let request     = BlockRetrievalRequest∙new me blockId numBlocks
          logIt fakeInfo -- ["to", lsA peer, lsBRQ request]
          let response    = ObmNeedFetch.writeRequestReadResponseUNSAFE nf me peer request
          -- TODO : sign response and check sig on response
          case response ^∙ brpStatus of λ where
            BRSSucceeded → do
              logIt fakeInfo -- (here [lsBRP response])
              vv ← use (lRoundManager ∙ rmEpochState ∙ esVerifier)
              -- LBFT-OBM-DIFF/TODO : this should live in a "network" module
              case BlockRetrieval.verify response (request ^∙ brqBlockId) (request ^∙ brqNumBlocks) vv of λ where
                (Left  e) → bail (withErrCtx (here' []) e)
                (Right _) → ok   (response ^∙ brpBlocks)
            BRSIdNotFound      → doLoop blockId attempt peers
            BRSNotEnoughBlocks → doLoop blockId attempt peers

  doLoop blockId attempt peers = do
    logIt fakeInfo -- (here' ["trying another peer", lsBRP response])
    loop blockId (attempt + 1) peers

  here' t = "BlockRetriever" ∷ "retrieveBlockForQCM" ∷ "NeedFetch" ∷ t
  logIt l = -- do
    logInfo l
    -- let x = Unsafe.unsafePerformIO (putStrLn @Text (show l))
    -- x `seq` pure x

pickPeer _ = λ where
  []       → Left fakeErr -- ["no more peers"]
  (p ∷ ps) → pure (p , ps)

