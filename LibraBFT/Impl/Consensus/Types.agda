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
-- One important trick here is that the RoundManager type separayes
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
  record RoundManagerEC : Set where
    constructor mkRoundManagerPreEC
    field
      ₋epSafetyRules  : SafetyRules
      ₋epValidators   : ValidatorVerifier
  open RoundManagerEC public
  unquoteDecl epSafetyRules epValidators = mkLens (quote RoundManagerEC)
    (epSafetyRules ∷ epValidators ∷ [])

  epEpoch : Lens RoundManagerEC EpochId
  epEpoch = epSafetyRules ∙ srPersistentStorage ∙ psEpoch

  epLastVotedRound : Lens RoundManagerEC Round
  epLastVotedRound = epSafetyRules ∙ srPersistentStorage ∙ psLastVotedRound

  -- We need enough authors to withstand the desired number of
  -- byzantine failures.  We enforce this with a predicate over
  -- 'RoundManagerEC'.
  RoundManagerEC-correct : RoundManagerEC → Set
  RoundManagerEC-correct epec =
    let numAuthors = kvm-size (epec ^∙ epValidators ∙ vvAddressToValidatorInfo)
        qsize      = epec ^∙ epValidators ∙ vvQuorumVotingPower
        bizF       = numAuthors ∸ qsize
     in suc (3 * bizF) ≤ numAuthors

  RoundManagerEC-correct-≡ : (epec1 : RoundManagerEC)
                             → (epec2 : RoundManagerEC)
                             → (epec1 ^∙ epValidators) ≡ (epec2 ^∙ epValidators)
                             → RoundManagerEC-correct epec1
                             → RoundManagerEC-correct epec2
  RoundManagerEC-correct-≡ epec1 epec2 refl = id

  -- Given a well-formed set of definitions that defines an EpochConfig,
  -- α-EC will compute this EpochConfig by abstracting away the unecessary
  -- pieces from RoundManagerEC.
  -- TODO-2: update and complete when definitions are updated to more recent version
  α-EC : Σ RoundManagerEC RoundManagerEC-correct → EpochConfig
  α-EC (epec , ok) =
    let numAuthors = kvm-size (epec ^∙ epValidators ∙ vvAddressToValidatorInfo)
        qsize      = epec ^∙ epValidators ∙ vvQuorumVotingPower
        bizF       = numAuthors ∸ qsize
     in (mkEpochConfig {! someHash?!}
                (epec ^∙ epEpoch) numAuthors {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!})

  postulate
    α-EC-≡ : (epec1  : RoundManagerEC)
           → (epec2  : RoundManagerEC)
           → (vals≡  : (epec1 ^∙ epValidators) ≡ (epec2 ^∙ epValidators))
           → (epoch≡ : (epec1 ^∙ epEpoch)      ≡ (epec2 ^∙ epEpoch))
           → (epec1-corr : RoundManagerEC-correct epec1)
           → α-EC (epec1 , epec1-corr) ≡ α-EC (epec2 , RoundManagerEC-correct-≡ epec1 epec2 vals≡ epec1-corr)
  {-
  α-EC-≡ epec1 epec2 refl refl epec1-corr = refl
  -}

  -- Finally, the RoundManager is split in two pieces: those
  -- that are used to make an EpochConfig versus those that
  -- use an EpochConfig.
  record RoundManager : Set where
    constructor mkRoundManager
    field
      ₋epEC           : RoundManagerEC
      ₋epEC-correct   : RoundManagerEC-correct ₋epEC
      ₋epWithEC       : RoundManagerWithEC (α-EC (₋epEC , ₋epEC-correct))
     -- If we want to add pieces that neither contribute to the
     -- construction of the EC nor need one, they should be defined in
     -- RoundManager directly
  open RoundManager public

  α-EC-EP : RoundManager → EpochConfig
  α-EC-EP ep = α-EC ((₋epEC ep) , (₋epEC-correct ep))

  ₋epHighestQC : (ep : RoundManager) → QuorumCert
  ₋epHighestQC ep = ₋btHighestQuorumCert ((₋epWithEC ep) ^∙ (lBlockTree (α-EC-EP ep)))

  epHighestQC : Lens RoundManager QuorumCert
  epHighestQC = mkLens' ₋epHighestQC
                        (λ (mkRoundManager ec ecc (mkRoundManagerWithEC (mkBlockStore bsInner))) qc
                          → mkRoundManager ec ecc (mkRoundManagerWithEC (mkBlockStore (record bsInner {₋btHighestQuorumCert = qc}))))

  ₋epHighestCommitQC : (ep : RoundManager) → QuorumCert
  ₋epHighestCommitQC ep = ₋btHighestCommitCert ((₋epWithEC ep) ^∙ (lBlockTree (α-EC-EP ep)))

  epHighestCommitQC : Lens RoundManager QuorumCert
  epHighestCommitQC = mkLens' ₋epHighestCommitQC
                        (λ (mkRoundManager ec ecc (mkRoundManagerWithEC (mkBlockStore bsInner))) qc
                          → mkRoundManager ec ecc (mkRoundManagerWithEC (mkBlockStore (record bsInner {₋btHighestCommitCert = qc}))))
