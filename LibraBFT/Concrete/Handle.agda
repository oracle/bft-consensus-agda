{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.NetworkMessages

module LibraBFT.Concrete.Handle
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  (ec      : EpochConfig)
   where

 open import LibraBFT.Concrete.EventProcessor hash hash-cr ec
 open import LibraBFT.Concrete.BlockTree hash hash-cr ec

 -- TODO: we should check if the block came from the right leader

 module _ (pre : EventProcessor) where

  handle-ver : VerNetworkRecord
             -- Output is a list of messages we want to send
             -- and a new state.
             → List NetworkMsg × EventProcessor
  handle-ver (C vc prf) = {!!}

{--
  handle-ver (B vb prf)
  -- We still need to look this block up and decide
  -- what to do if we already have this block
    with extends-B? (ec pre) (rss pre) vb {!!}
  ...| nothing  = {!!} -- what do we do if it doesn't extend?
  ...| just ext 
     -- If it does extend, though, we insert it.
     = ([] , record pre { rss = insert (ec pre) (rss pre) (B vb) ext })
  handle-ver _ = {!!} -- TODO: finish
--}

  handle : NetworkMsg -- msg addressed for 'us'
         → List NetworkMsg × EventProcessor
  handle msg
    with check-signature-and-format (content msg)
  ...| nothing  = ([] , pre) 
  ...| just ver = handle-ver ver

