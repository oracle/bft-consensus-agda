{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Haskell.Modules.RWS.RustAnyHow
open import LibraBFT.Base.Types
open import LibraBFT.Impl.Consensus.EpochManagerTypes
import      LibraBFT.Impl.OBM.ECP-LBFT-OBM-Diff.ECP-LBFT-OBM-Diff-0 as ECP-LBFT-OBM-Diff-0
open import LibraBFT.Impl.OBM.Logging.Logging
import      LibraBFT.Impl.Storage.DiemDB.DiemDB                     as DiemDB
import      LibraBFT.Impl.Types.EpochChangeProof                    as EpochChangeProof
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.ImplShared.Interface.Output
open import LibraBFT.ImplShared.Util.Dijkstra.All
open import LibraBFT.Prelude
open import Optics.All
------------------------------------------------------------------------------
open import Data.String                                            using (String)

module LibraBFT.Impl.OBM.ECP-LBFT-OBM-Diff.ECP-LBFT-OBM-Diff-1 where

------------------------------------------------------------------------------

postulate -- TODO-1 : nub (remove duplicates)
  nub : ∀ {A : Set} → List A → List A

------------------------------------------------------------------------------

amIMemberOfCurrentEpoch : Author → List Author → Bool
amIMemberOfCurrentEpochM : LBFT Bool

------------------------------------------------------------------------------

e_SyncManager_insertQuorumCertM_commit : LedgerInfoWithSignatures → LBFT (Either ErrLog Unit)
e_SyncManager_insertQuorumCertM_commit liws =
  ifD (not ECP-LBFT-OBM-Diff-0.enabled)
  then (do
    rcvrs ← use (lRoundManager ∙ rmObmAllAuthors)
    --act (BroadcastEpochChangeProof (EpochChangeProof∙new (liws ∷ []) false) rcvrs) -- TODO-1
    ok unit)
  else do
    {-
    LBFT-OBM-DIFF
    A SyncInfo is sent BEFORE an EpochChangeProof.
    Only sent to members of current epoch (not the one the EpochChangeProof will transition to).

    This is needed since the highest committed QC from the initial committer/leader of
    the EPOCHCHANGE transaction needs to be given to followers so they will also
    commit the EPOCHCHANGE transaction.

    Note: This is similar to how the QC is carried in a ProposalMsg.
    -}
    rcvrs    ← use (lRoundManager ∙ rmObmAllAuthors)
    syncInfo ← SyncInfo∙new <$> use (lBlockStore ∙ bsHighestQuorumCert)
                            <*> use (lBlockStore ∙ bsHighestCommitCert)
                            <*> use (lBlockStore ∙ bsHighestTimeoutCert)
    act (BroadcastSyncInfo syncInfo rcvrs)

    -- LBFT-OBM-DIFF : PUSH: when sending an ECP when committing an epoch change,
    -- send all epoch ending ledger info (not just the current one)
    -- so the receiver will be up-to-date.
    -- TODO : optimize: let receiver PULL its gaps.
    db ← use (lBlockStore ∙ bsStorage ∙ msObmDiemDB)
    maybeSD (liws ^∙ liwsLedgerInfo ∙ liNextEpochState) (bail fakeErr {-"liNextEpochState" ∷ "Nothing" ∷ []-}) $ λ es → do
      let newRcvrs = es ^∙ esVerifier ∙ vvObmAuthors
          allRcvrs = nub (rcvrs ++ newRcvrs)
      eitherS (DiemDB.getEpochEndingLedgerInfos db ({-Epoch-} 1) (liws ^∙ liwsEpoch + 1))
              bail
              (λ (liwss , b) -> do
                  -- act (BroadcastEpochChangeProof lEC (EpochChangeProof.new liwss b) allRcvrs) -- TODO-1
                  ok unit)
 where
  here' : List String → List String
  here' t = "e_SyncManager_InsertQuorumCertM_commit" ∷ t

------------------------------------------------------------------------------

e_RoundState_processLocalTimeoutM : Epoch → Round → LBFT Bool
e_RoundState_processLocalTimeoutM e r =
  ifD not ECP-LBFT-OBM-Diff-0.enabled
  then yes'
  else
    -- LBFT-OBM-DIFF : do not broadcast timeouts if not member of epoch
    ifMD amIMemberOfCurrentEpochM
         yes'
         (do
           logInfo fakeInfo -- ["not a member of Epoch", "ignoring timeout", lsE e, lsR r]
           pure false)
 where
  yes' : LBFT Bool
  yes' = do
    logInfo fakeInfo -- InfoRoundTimeout e r
    pure true

------------------------------------------------------------------------------
-- TODO-1 : use EitherD
e_EpochManager_doECP_waitForRlec : EpochManager → EpochChangeProof → Either ErrLog Bool
e_EpochManager_doECP_waitForRlec self ecp =
  if not ECP-LBFT-OBM-Diff-0.enabled
  then pure true
  else do
    rm ← self ^∙ emObmRoundManager
    e  ← self ^∙ emEpoch
    maybeS (rm ^∙ rmObmMe)
           (Left fakeErr {-["e_EpochManager_doECP_waitForRlec", "rmObmMe", "Nothing"]-})
           $ λ me → let m = amIMemberOfCurrentEpoch me (rm ^∙ rmObmAllAuthors)
                     in pure (m ∧ (EpochChangeProof.obmLastEpoch ecp == e))

------------------------------------------------------------------------------

module e_EpochManager_startNewEpoch where
  VariantFor : ∀ {ℓ} EL → EL-func {ℓ} EL
  VariantFor EL =
    EpochManager → EpochChangeProof
    → EL ErrLog EpochManager

  step₀ : VariantFor EitherD
  step₀ self ecp =
    ifD not ECP-LBFT-OBM-Diff-0.enabled
    then pure self
    else do
      -- LBFT-OBM-DIFF: store all the epoch ending LedgerInfos sent in ECP
      -- (to avoid gaps -- from when a node is not a member).
      db ← (foldM) (\db l → DiemDB.saveTransactions db (just l))
                    (self ^∙ emStorage ∙ msObmDiemDB)
                    (ecp ^∙ ecpLedgerInfoWithSigs)
      pure (self & emStorage ∙ msObmDiemDB ∙~ db)

e_EpochManager_startNewEpoch      : e_EpochManager_startNewEpoch.VariantFor Either
e_EpochManager_startNewEpoch em   = toEither ∘ e_EpochManager_startNewEpoch.step₀ em

e_EpochManager_startNewEpoch-D    : e_EpochManager_startNewEpoch.VariantFor EitherD
e_EpochManager_startNewEpoch-D em = fromEither ∘ e_EpochManager_startNewEpoch em

------------------------------------------------------------------------------
-- TODO-1 : use EitherD
e_EpochManager_checkEpc : EpochManager → EpochChangeProof → Either ErrLog Unit
e_EpochManager_checkEpc self ecp =
  if (not ECP-LBFT-OBM-Diff-0.enabled)
  then checkEpcNot
  else checkEpcEnable
 where
  here' : List String → List String

  checkEpcNot : Either ErrLog Unit
  checkEpcNot = case EpochChangeProof.epoch ecp of λ where
    (Left e) → Left (withErrCtx (here' []) e)
    (Right msgEpoch) → do
      e ← self ^∙ emEpoch
      if msgEpoch == e
        then pure unit
        else Left fakeErr
              --(ErrInfo (lEC, InfoL (here ["unexpected epoch proof", lsE msgEpoch, lsE e])))

  -- LBFT-OBM-DIFF : ignore it if it doesn't help
  checkEpcEnable : Either ErrLog Unit
  checkEpcEnable = do
    epoch ← self ^∙ emEpoch
    if-dec (EpochChangeProof.obmLastEpoch ecp <? epoch)
      then Left fakeErr
          --(ErrInfo (lEC, InfoL (here [ "ecp last", lsE (EpochChangeProof.obmLastEpoch ecp)
          --                           , "< ours"  , lsE epoch ])))
      else pure unit

  here' t = "e_EpochManager_checkEpc" ∷ t


------------------------------------------------------------------------------
-- TODO-1 : use EitherD
e_EpochManager_processMessage_ISyncInfo : EpochManager → SyncInfo → Either ErrLog Unit
e_EpochManager_processMessage_ISyncInfo self si = do
  e ← self ^∙ emEpoch
  grd‖ not ECP-LBFT-OBM-Diff-0.enabled ≔ pure unit
     ‖ si ^∙ siEpoch == e              ≔ pure unit
     ‖ otherwise≔
       Left fakeErr
             -- ["si epoch", lsE (si^.siEpoch), "/=", "ours", lsE e]

------------------------------------------------------------------------------

amIMemberOfCurrentEpochM =
  use (lRoundManager ∙ rmObmMe) >>= λ where
    nothing → do
      logErr fakeErr -- no identity
      pure false
    (just me) →
      amIMemberOfCurrentEpoch <$> pure me <*> use (lRoundManager ∙ rmObmAllAuthors)

amIMemberOfCurrentEpoch = elem
