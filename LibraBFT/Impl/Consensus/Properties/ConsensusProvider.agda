open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
import      LibraBFT.Impl.Consensus.ConsensusProvider      as ConsensusProvider
open import LibraBFT.Impl.Properties.Util
import      LibraBFT.Impl.Types.ValidatorVerifier          as ValidatorVerifier
import      LibraBFT.Impl.IO.OBM.GenKeyFile                as GenKeyFile
open import LibraBFT.Impl.OBM.Logging.Logging
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Consensus.Types.EpochDep
open import LibraBFT.ImplShared.Consensus.Types.EpochIndep
open import LibraBFT.ImplShared.Util.Util
open import LibraBFT.Prelude                               hiding (_++_)
open import Optics.All

module LibraBFT.Impl.Consensus.Properties.ConsensusProvider where

open InitProofDefs

module startConsensusSpec
  (nodeConfig : NodeConfig)
  (now        : Instant)
  (payload    : OnChainConfigPayload)
  (liws       : LedgerInfoWithSignatures)
  (sk         : SK)
  (needFetch  : ObmNeedFetch)
  (propGen    : ProposalGenerator)
  (stateComp  : StateComputer)
  where

  record Requirements : Set where
    constructor mkRequirements
    field
      vv     : ValidatorVerifier
      vvCorr : ValidatorVerifier.from-e-abs (payload ^∙ occpObmValidatorSet) ≡ Right vv

  module _ (reqs : Requirements) where
    -- TODO-2: Requires refinement.  Needs additional Requirements.
    postulate
     contract' : EitherD-weakestPre (ConsensusProvider.startConsensus-ed-abs
                                      nodeConfig now payload liws sk needFetch propGen stateComp)
                                    (InitContract nothing)
