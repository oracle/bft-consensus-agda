{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
------------------------------------------------------------------------------
open import Data.String                         using (String)

module LibraBFT.Impl.IO.OBM.Messages where

record ECPWire : Set where
  constructor ECPWire∙new
  field
    --_ecpwWhy    : Text           -- for log visualization
    --_ecpwEpoch  : Epoch          -- for log visualization; epoch of sender
    --_ecpwRound  : Round          -- for log visualization; round of sender
    _ecpwECP      : EpochChangeProof
-- instance S.Serialize ECPWire

record EpRRqWire : Set where
  constructor EpRRqWire∙new
  field
    --_eprrqwWhy  : Text           -- for log visualization
    --_eprrqEpoch : Epoch          -- for log visualization; epoch of sender
    --_eprrqRound : Round          -- for log visualization; round of sender
    _eprrqEpRRq   : EpochRetrievalRequest
-- instance S.Serialize EpRRqWire

data Input : Set where
  IBlockRetrievalRequest    : Instant                  →          BlockRetrievalRequest  → Input
  IBlockRetrievalResponse   : Instant                  →          BlockRetrievalResponse → Input
  IEpochChangeProof         :           AccountAddress →          ECPWire                → Input
  IEpochRetrievalRequest    :           AccountAddress →          EpRRqWire              → Input
  IInit                     : Instant                                                    → Input
  IProposal                 : Instant → AccountAddress →          ProposalMsg            → Input
  IReconfigLocalEpochChange :                                   ReconfigEventEpochChange → Input
  ISyncInfo                 : Instant → AccountAddress →          SyncInfo               → Input
  ITimeout                  : Instant → String {-String is ThreadId-} → Epoch → Round    → Input
  IVote                     : Instant → AccountAddress →          VoteMsg                → Input

