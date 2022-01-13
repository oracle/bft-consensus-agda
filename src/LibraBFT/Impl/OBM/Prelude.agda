{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import Util.KVMap as Map
open import Util.Prelude

module LibraBFT.Impl.OBM.Prelude where

lookupOrInsert : ∀ {K V : Set} → K → V → Map.KVMap K V → Map.KVMap K V
lookupOrInsert k v m =
  if Map.kvm-member k m
  then m
  else Map.insert k v m
