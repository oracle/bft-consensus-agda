{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.Base.ByteString
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Types
open import LibraBFT.Hash
open import LibraBFT.Impl.Base.Types
open import LibraBFT.Impl.Consensus.BlockStorage.BlockStore as BlockStore
open import LibraBFT.Impl.Consensus.ConsensusTypes.Vote as Vote
open import LibraBFT.Impl.Consensus.Types
open import LibraBFT.Impl.Util.Crypto
open import LibraBFT.Impl.Util.Util
open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Prelude
open import Optics.All

module LibraBFT.Impl.OBM.Prelude where

open RWST-do

maybeS   : ∀ {a b : Set} →       Maybe a  →      b → (a →      b) →      b
maybeSM  : ∀ {a b : Set} → LBFT (Maybe a) → LBFT b → (a → LBFT b) → LBFT b
maybeSMP : ∀ {a b : Set} → LBFT (Maybe a) →      b → (a → LBFT b) → LBFT b

-- maybeS(wap)
maybeS    ma  b f = maybe′ (const b) b ma
-- maybeS(wap)M(onad)
maybeSM  mma mb f = do
  ma ← mma
  case ma of λ where
    nothing →  mb
    (just j) → f j
-- maybeS(wap)M(onad)P(ure) -- just wraps default in 'pure'
maybeSMP mma  b f = do
  ma ← mma
  case ma of λ where
    nothing  → pure b
    (just j) → f j
