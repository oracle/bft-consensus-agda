open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Base.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS
open import LibraBFT.Concrete.Network

module LibraBFT.Concrete.Handle
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
   where

 open import LibraBFT.Concrete.NodeState hash hash-cr
 open import LibraBFT.Concrete.RecordStoreState hash hash-cr

 -- TODO: we should check if the block came from the right leader

 module _ (pre : NodeState) where

  open import LibraBFT.Abstract.Records (ec pre)

  handle-ver : VerNetworkRecord (ec pre)
             -- Output is a list of messages we want to send
             -- and a new state.
             → List NetworkMsg × NodeState
  handle-ver (B vb prf)
  -- We still need to look this block up and decide
  -- what to do if we already have this block
    with extends-B? (ec pre) (rss pre) vb {!!}
  ...| nothing  = {!!} -- what do we do if it doesn't extend?
  ...| just ext 
     -- If it does extend, though, we insert it.
     = ([] , record pre { rss = insert (ec pre) (rss pre) (B vb) ext })
  handle-ver _ = {!!} -- TODO: finish

  handle : NetworkMsg -- msg addressed for 'us'
         → List NetworkMsg × NodeState
  handle msg
    with check-signature-and-format (ec pre) (content msg)
  ...| nothing  = ([] , pre) 
  ...| just ver = handle-ver ver

