{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Consensus.Types

module LibraBFT.Impl.IO.OBM.ObmNeedFetch where

{-
The functions in this module are used when a node needs to catchup.

TODO-3: model catchup request/response in Agda.

In haskell, for each message received from the network (including messages to self),
each message is processed in a single thread that completes the processing
before then processing a subsequent message.

However, a node detects that it needs to catchup "in the middle" of that processing.
In Haskell we use unsafePerformIO to send a network request to other nodes asking
for "catchup" data.

The responses are received by a different thread that then feeds them to the waiting thread,
which then proceeds.
-}

postulate -- TODO-3: writeRequestReadResponseUNSAFE
  writeRequestReadResponseUNSAFE
    : ObmNeedFetch → Author → Author → BlockRetrievalRequest
    → BlockRetrievalResponse


