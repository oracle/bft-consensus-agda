{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types
open import LibraBFT.Base.Encode
open import LibraBFT.Base.PKCS

open import LibraBFT.Concrete.Records
open import LibraBFT.Concrete.Consensus.Types
open import LibraBFT.Concrete.Consensus.ChainedBFT.EventProcessor

module LibraBFT.Concrete.Handle
  (hash    : ByteString → Hash)
  (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  (ec      : EpochConfig)
   where

 open import LibraBFT.Concrete.BlockTree hash hash-cr ec

 -- TODO: we should check if the block came from the right leader

 postulate
   now : Instant  -- TODO: get real timestamp

 handle-ver : ⦃ encA : Encoder TX ⦄
            → {pre : EventProcessor TX}
            → VerNetworkMsg TX
            -- Output is a list of messages we want to send
            -- and a new state.
            → List (Action TX) × EventProcessor TX
 handle-ver {pre = pre} (P p , wnm)
    with processProposalMsg now p {pre} {[]}
 ...| _ , post , acts = acts , post
 handle-ver {pre = pre} (V v , wnm) = {!!}
 handle-ver {pre = pre} (C c , wnm) = {!!}

 handle : ⦃ encA : Encoder TX ⦄
        → {pre : EventProcessor TX}
        → NetworkMsg TX -- msg addressed for 'us'
        → List (Action TX) × EventProcessor TX
 handle {pre = pre} msg
   with check-signature {!!} msg   -- TODO: figure out where to get public key from
 ...| nothing  = ([] , pre)
 ...| just ver = handle-ver {pre = pre} (msg , ver)
