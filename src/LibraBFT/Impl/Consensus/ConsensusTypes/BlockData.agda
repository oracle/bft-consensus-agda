{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Impl.Crypto.Crypto.Hash    as Hash
open import LibraBFT.ImplShared.Consensus.Types
open import Optics.All
open import Util.KVMap                          as Map
open import Util.PKCS
open import Util.Prelude
open import Util.Types

module LibraBFT.Impl.Consensus.ConsensusTypes.BlockData where

------------------------------------------------------------------------------

newGenesis : {-Instant →-} QuorumCert → BlockData

------------------------------------------------------------------------------

newGenesisFromLedgerInfo : LedgerInfo → Either ErrLog BlockData
newGenesisFromLedgerInfo li =
  if not (li ^∙ liEndsEpoch)
  then Left fakeErr -- ["BlockData", "newGenesisFromLedgerInfo", "liNextEpochState == Nothing"]
  else
    let ancestor          = BlockInfo∙new
                              (li ^∙ liEpoch)
                              {-Round-} 0
                              Hash.valueZero
                              (li ^∙ liTransactionAccumulatorHash)
                              (li ^∙ liVersion)
                            --(li ^∙ liTimestamp)
                              nothing
        genesisQuorumCert = QuorumCert∙new
                              (VoteData∙new ancestor ancestor)
                              (LedgerInfoWithSignatures∙new
                               (LedgerInfo∙new ancestor Hash.valueZero) Map.empty)
     in pure $ newGenesis {-(li ^∙ liTimestamp)-} genesisQuorumCert

newGenesis {-timestamp-} qc = BlockData∙new
  (qc ^∙ qcCertifiedBlock ∙ biEpoch + 1)
  {-Round-} 0
--timestamp
  qc
  Genesis

newNil : Round → QuorumCert → BlockData
newNil r qc = BlockData∙new
  (qc ^∙ qcCertifiedBlock ∙ biEpoch)
  r
--(qc ^∙ qcCertifiedBlock ∙ biTimestamp)
  qc
  NilBlock

newProposal : TX → Author → Round → {-Instant →-} QuorumCert → BlockData
newProposal payload author round {-timestamp-} quorumCert = BlockData∙new
  (quorumCert ^∙ qcCertifiedBlock ∙ biEpoch) round {-timestamp-} quorumCert (Proposal payload author)

isGenesisBlock : BlockData → Bool
isGenesisBlock bd = bd ^∙ bdBlockType == Genesis

isNilBlock : BlockData → Bool
isNilBlock bd = bd ^∙ bdBlockType == NilBlock
