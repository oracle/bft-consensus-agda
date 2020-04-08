{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.Consensus.Types

open import LibraBFT.Concrete.OBM.Util

open RWST-do

module LibraBFT.Concrete.Handle
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

 open import LibraBFT.Concrete.Consensus.ChainedBFT.EventProcessor hash hash-cr
 open import LibraBFT.Concrete.NetworkMsg

 handle : NetworkMsg → Instant → LBFT Unit
 handle msg now
   with check-signature {!!} msg   -- TODO: figure out where to get public key from
 ...| nothing  = return unit       -- Can't verify signature, do nothing, maybe logging?
 ...| just ver with msg
 ...| P p = processProposalMsg now p
 ...| V v = processVote now v
 ...| C c = return unit            -- We don't do anything with commit messages, they are just for defining Correctness.

 -- The 'handle' function as a Mealy Machine
 handle-mm : NetworkMsg → Instant → EventProcessor → EventProcessor × List Action
 handle-mm msg i st = let (_ , st' , acts) = RWST-run (handle msg i) unit st
                       in st' , acts

 -- Actions are processed into a list of messages
 processActionMsgs : EventProcessor → Action → List (Author × NetworkMsg)
 processActionMsgs st act = {!!} 

 -- And ultimately, the all-knowing system layer only cares about the
 -- step function.
 step : NetworkMsg → Instant → EventProcessor 
      → EventProcessor × List (Author × NetworkMsg)
 step msg i st = let (st' , acts) = handle-mm msg i st
                  in (st' , concat (List-map (processActionMsgs st') acts))
