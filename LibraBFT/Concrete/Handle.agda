{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import LibraBFT.Concrete.Consensus.Types

open import LibraBFT.Concrete.OBM.Util

open RWST-do

module LibraBFT.Concrete.Handle where

 open import LibraBFT.Concrete.Consensus.ChainedBFT.EventProcessor
 open import LibraBFT.Concrete.Records

 handle : NetworkMsg
        → Instant
        → LBFT Unit
 handle msg now
   with check-signature {!!} msg   -- TODO: figure out where to get public key from
 ...| nothing  = return unit       -- Can't verify signature, do nothing, maybe logging?
 ...| just ver with msg
 ...| P p = processProposalMsg now p
 ...| V v = processVote now v
 ...| C c = return unit            -- We don't do anything with commit messages, they are just for defining Correctness.
