{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.TestUtils.MockStorage as MockStorage
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                                   as String

module LibraBFT.Impl.Consensus.PersistentLivenessStorage where

------------------------------------------------------------------------------

obmUpdateM
  : ( PersistentLivenessStorage → LBFT (Either ErrLog PersistentLivenessStorage) )
  → LBFT (Either ErrLog Unit)

obmUpdateE
  : BlockStore
  → ( PersistentLivenessStorage
       → Either ErrLog PersistentLivenessStorage )
  -> Either ErrLog BlockStore

------------------------------------------------------------------------------

saveTreeM : List Block → List QuorumCert → LBFT (Either ErrLog Unit)
saveTreeM blocks qcs =
  obmUpdateM (MockStorage.saveTreeM blocks qcs)

saveTreeE : BlockStore → List Block → List QuorumCert → Either ErrLog BlockStore
saveTreeE bs blocks qcs =
  obmUpdateE bs (MockStorage.saveTreeE blocks qcs)

pruneTreeM : List HashValue → LBFT (Either ErrLog Unit)
pruneTreeM =
  obmUpdateM ∘ MockStorage.pruneTreeM

saveVoteM : Vote → LBFT (Either ErrLog Unit)
saveVoteM =
  obmUpdateM ∘ MockStorage.saveStateM

startM : LBFT (Either ErrLog RecoveryData)
startM =
  use (lBlockStore ∙ bsStorage) >>= λ s → pure (MockStorage.start s) ∙^∙ withErrCtx (here' [])
 where
  here' : List String.String → List String.String
  here' t = "PersistentLivenessStorage" ∷ "startM" ∷ t

saveHighestTimeoutCertM : TimeoutCertificate → LBFT (Either ErrLog Unit)
saveHighestTimeoutCertM =
  obmUpdateM ∘ MockStorage.saveHighestTimeoutCertificateM

------------------------------------------------------------------------------

obmUpdateM f = do
  s <- use (lBlockStore ∙ bsStorage)
  f s ∙?∙ λ s' → do lBlockStore ∙ bsStorage ∙= s'; ok unit

obmUpdateE bs f = do
  let s = bs ^∙ bsStorage
  s'    ← f s
  pure (bs & bsStorage ∙~ s')
