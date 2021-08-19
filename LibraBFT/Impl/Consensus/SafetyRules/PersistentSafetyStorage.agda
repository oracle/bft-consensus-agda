{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

------------------------------------------------------------------------------
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.Consensus.ConsensusTypes.Block      as Block
import      LibraBFT.Impl.Consensus.ConsensusTypes.QuorumCert as QuorumCert
import      LibraBFT.Impl.Consensus.ConsensusTypes.Vote       as Vote
import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteData   as VoteData
import      LibraBFT.Impl.OBM.Crypto                          as Crypto
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.Impl.Types.BlockInfo                     as BlockInfo
open import LibraBFT.Impl.Types.ValidatorSigner               as ValidatorSigner
open import LibraBFT.ImplShared.Base.Types
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
import      LibraBFT.ImplShared.Util.Crypto                   as Crypto
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
import      Data.String                                       as String
------------------------------------------------------------------------------

module LibraBFT.Impl.Consensus.SafetyRules.PersistentSafetyStorage where

new : Author → Waypoint → SK → PersistentSafetyStorage
new author waypoint sk = mkPersistentSafetyStorage
     {- _pssSafetyData =-} (SafetyData∙new
                           {-  _sdEpoch          = Epoch-} 1
                           {-, _sdLastVotedRound = Round-} 0
                           {-, _sdPreferredRound = Round-} 0
                           {-, _sdLastVote       =-}       nothing)
     {-, _pssAuthor    =-} author
     {-, _pssWaypoint  =-} waypoint
     {-, _pssObmSK     =-} (just sk)
