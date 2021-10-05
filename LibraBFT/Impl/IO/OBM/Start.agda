{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.Consensus.ConsensusProvider as ConsensusProvider
import      LibraBFT.Impl.IO.OBM.GenKeyFile           as GenKeyFile
import      LibraBFT.Impl.IO.OBM.ObmNeedFetch         as ObmNeedFetch
import      LibraBFT.Impl.Types.ValidatorSigner       as ValidatorSigner
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.IO.OBM.Start where

{-
This only does the initialization steps from the Haskell version.
If initialization succeeds, it returns
- the EpochManager (for all epochs)
  - note: this contains the initialized RoundManager for the current epoch (i.e., Epoch 0)
- any output from the RoundManager produced during initialization

The only output is (with info logging removed):

-- only the leader of round 1 will broadcast a proposal
BroadcastProposal; [ ... peer addresses ... ];
                   (ProposalMsg
                     (B 7194dca (BD 1 1 (Prop ("TX/1/1")) ...)) -- proposed block
                     (SI (hqc c66a132) (hcc N) (htc (TC N))))   -- SyncInfo

The Haskell code, after initialization, hooks up the communication channels and sockets
and starts threads that handle them.  One of the threads is given to
EpochManager.obmStartLoop to get input and pass it through the EpochManager
and then (usually) on to the RoundMnager.

TODO-3: Replace 'Handle.initRM' with the initialized RoundManager obtained
through the following 'startViaConsensusProvider'.
TODO-3: Figure out how to handle the initial BroadcastProposal.
-}
startViaConsensusProvider
  : Instant
  → GenKeyFile.NfLiwsVsVvPe
  → TxTypeDependentStuffForNetwork
  → Either ErrLog (EpochManager × List Output)
startViaConsensusProvider now (nf , liws , vs , vv , pe) txTDS = do
  (nc , occp , _liws , sk , _pe) ← ConsensusProvider.obmInitialData (nf , liws , vs , vv , pe)
  ConsensusProvider.startConsensus
    nc now occp liws sk
    (ObmNeedFetch∙new {- newNetwork -stps'-})
    (txTDS ^∙ ttdsnProposalGenerator) (txTDS ^∙ ttdsnStateComputer)

