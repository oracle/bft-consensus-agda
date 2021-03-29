{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Optics.All
open import LibraBFT.Prelude
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Base.KVMap as KVMap
open import LibraBFT.Base.Types
open import Data.String using (String)

-- This module defines types for an out-of-date implementation, based
-- on a previous version of LibraBFT.  It will be updated to model a
-- more recent version in future.
--
-- One important trick here is that the EventProcessor type separayes
-- types that /define/ the EpochConfig and types that /use/ the
-- /EpochConfig/. The advantage of doing this separation can be seen
-- in Util.Util.liftEC, where we define a lifting of a function that
-- does not change the bits that define the EpochConfig into the whole
-- state.  This enables a more elegant approach for reasoning about
-- functions that do not change parts of the state responsible for
-- defining the epoch config.  However, the separation is not perfect,
-- so sometimes fields may be modified in EpochIndep even though there
-- is no epoch change.

module LibraBFT.Impl.Consensus.Types where
  open import LibraBFT.Impl.Base.Types                       public
  open import LibraBFT.Impl.NetworkMsg                       public
  open import LibraBFT.Abstract.Types.EpochConfig UID NodeId public
  open import LibraBFT.Impl.Consensus.Types.EpochIndep       public
  open import LibraBFT.Impl.Consensus.Types.EpochDep         public

  -- The parts of the state of a peer that are used to
  -- define the EpochConfig are the SafetyRules and ValidatorVerifier:
  record EventProcessorEC : Set where
    constructor mkEventProcessorPreEC
    field
      ₋epSafetyRules  : SafetyRules
      ₋epValidators   : ValidatorVerifier
  open EventProcessorEC public
  unquoteDecl epSafetyRules epValidators = mkLens (quote EventProcessorEC)
    (epSafetyRules ∷ epValidators ∷ [])

  epEpoch : Lens EventProcessorEC EpochId
  epEpoch = epSafetyRules ∙ srPersistentStorage ∙ psEpoch

  epLastVotedRound : Lens EventProcessorEC Round
  epLastVotedRound = epSafetyRules ∙ srPersistentStorage ∙ psLastVotedRound

  -- We need enough authors to withstand the desired number of
  -- byzantine failures.  We enforce this with a predicate over
  -- 'EventProcessorEC'.
  EventProcessorEC-correct : EventProcessorEC → Set
  EventProcessorEC-correct epec =
    let numAuthors = kvm-size (epec ^∙ epValidators ∙ vvAddressToValidatorInfo)
        qsize      = epec ^∙ epValidators ∙ vvQuorumVotingPower
        bizF       = numAuthors ∸ qsize
     in suc (3 * bizF) ≤ numAuthors

  EventProcessorEC-correct-≡ : (epec1 : EventProcessorEC)
                             → (epec2 : EventProcessorEC)
                             → (epec1 ^∙ epValidators) ≡ (epec2 ^∙ epValidators)
                             → EventProcessorEC-correct epec1
                             → EventProcessorEC-correct epec2
  EventProcessorEC-correct-≡ epec1 epec2 refl = id

  -- Given a well-formed set of definitions that defines an EpochConfig,
  -- α-EC will compute this EpochConfig by abstracting away the unecessary
  -- pieces from EventProcessorEC.
  -- TODO-2: update and complete when definitions are updated to more recent version
  α-EC : Σ EventProcessorEC EventProcessorEC-correct → EpochConfig
  α-EC (epec , ok) =
    let numAuthors = kvm-size (epec ^∙ epValidators ∙ vvAddressToValidatorInfo)
        qsize      = epec ^∙ epValidators ∙ vvQuorumVotingPower
        bizF       = numAuthors ∸ qsize
     in (mkEpochConfig {! someHash?!}
                (epec ^∙ epEpoch) numAuthors {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!})

  postulate
    α-EC-≡ : (epec1  : EventProcessorEC)
           → (epec2  : EventProcessorEC)
           → (vals≡  : (epec1 ^∙ epValidators) ≡ (epec2 ^∙ epValidators))
           → (epoch≡ : (epec1 ^∙ epEpoch)      ≡ (epec2 ^∙ epEpoch))
           → (epec1-corr : EventProcessorEC-correct epec1)
           → α-EC (epec1 , epec1-corr) ≡ α-EC (epec2 , EventProcessorEC-correct-≡ epec1 epec2 vals≡ epec1-corr)
  {-
  α-EC-≡ epec1 epec2 refl refl epec1-corr = refl
  -}

  -- Finally, the EventProcessor is split in two pieces: those
  -- that are used to make an EpochConfig versus those that
  -- use an EpochConfig.
  record EventProcessor : Set where
    constructor mkEventProcessor
    field
      ₋epEC           : EventProcessorEC
      ₋epEC-correct   : EventProcessorEC-correct ₋epEC
      ₋epWithEC       : EventProcessorWithEC (α-EC (₋epEC , ₋epEC-correct))
     -- If we want to add pieces that neither contribute to the
     -- construction of the EC nor need one, they should be defined in
     -- EventProcessor directly
  open EventProcessor public

  α-EC-EP : EventProcessor → EpochConfig
  α-EC-EP ep = α-EC ((₋epEC ep) , (₋epEC-correct ep))

  ₋epHighestQC : (ep : EventProcessor) → QuorumCert
  ₋epHighestQC ep = ₋btHighestQuorumCert ((₋epWithEC ep) ^∙ (lBlockTree (α-EC-EP ep)))

  epHighestQC : Lens EventProcessor QuorumCert
  epHighestQC = mkLens' ₋epHighestQC
                        (λ (mkEventProcessor ec ecc (mkEventProcessorWithEC (mkBlockStore bsInner))) qc
                          → mkEventProcessor ec ecc (mkEventProcessorWithEC (mkBlockStore (record bsInner {₋btHighestQuorumCert = qc}))))

  ₋epHighestCommitQC : (ep : EventProcessor) → QuorumCert
  ₋epHighestCommitQC ep = ₋btHighestCommitCert ((₋epWithEC ep) ^∙ (lBlockTree (α-EC-EP ep)))

  epHighestCommitQC : Lens EventProcessor QuorumCert
  epHighestCommitQC = mkLens' ₋epHighestCommitQC
                        (λ (mkEventProcessor ec ecc (mkEventProcessorWithEC (mkBlockStore bsInner))) qc
                          → mkEventProcessor ec ecc (mkEventProcessorWithEC (mkBlockStore (record bsInner {₋btHighestCommitCert = qc}))))
