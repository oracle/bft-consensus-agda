{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

import      LibraBFT.Impl.Consensus.ConsensusTypes.VoteData as VoteData
open import LibraBFT.Impl.OBM.Crypto                        hiding (verify)
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Types.ValidatorVerifier           as ValidatorVerifier
open import LibraBFT.ImplShared.Consensus.Types
open import Optics.All
open import Util.Hash
open import Util.PKCS                                       hiding (verify)
open import Util.Prelude
------------------------------------------------------------------------------
open import Data.String                                     using (String)

module LibraBFT.Impl.Consensus.ConsensusTypes.Vote where

------------------------------------------------------------------------------

timeout : Vote → Timeout

------------------------------------------------------------------------------

newWithSignature : VoteData → Author → LedgerInfo → Signature → Vote
newWithSignature voteData author ledgerInfo signature =
  Vote∙new voteData author ledgerInfo signature nothing

verify : Vote → ValidatorVerifier → Either ErrLog Unit
verify self validator = do
  lcheck (self ^∙ vLedgerInfo ∙ liConsensusDataHash == hashVD (self ^∙ vVoteData))
         (here' ("Vote's hash mismatch with LedgerInfo" ∷ []))
  withErrCtx' (here' ("vote" ∷ []))
    (ValidatorVerifier.verify validator (self ^∙ vAuthor) (self ^∙ vLedgerInfo) (self ^∙ vSignature))
  case self ^∙ vTimeoutSignature of λ where
    nothing    → pure unit
    (just tos) →
      withErrCtx' (here' ("timeout" ∷ []))
        (ValidatorVerifier.verify validator (self ^∙ vAuthor) (timeout self) tos)
  withErrCtx' (here' ("VoteData" ∷ [])) (VoteData.verify (self ^∙ vVoteData))
 where
  here' : List String → List String
  here' t = "Vote" ∷ "verify" ∷ "failed" {-∷lsV self-} ∷ t

addTimeoutSignature : Vote → Signature → Vote
addTimeoutSignature self sig =
  if is-just (self ^∙ vTimeoutSignature)
  then self
  else self & vTimeoutSignature ?~ sig

timeout v =
  Timeout∙new (v ^∙ vVoteData ∙ vdProposed ∙ biEpoch) (v ^∙ vVoteData ∙ vdProposed ∙ biRound)

isTimeout : Vote → Bool
isTimeout v = is-just (v ^∙ vTimeoutSignature)



