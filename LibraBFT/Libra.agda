{-# OPTIONS --allow-unsolved-metas #-}

open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas

-- |The final correctness proof of LibraBFT
module LibraBFT.Libra
   (#peer   : ℕ)
   (hash    : ByteString → Hash)
   (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
 where

 -- The Libra model arises as an instantiation of the SystemModel
 -- to the Libra.handle function.

 open import LibraBFT.Concrete.NetworkMsg
 open import LibraBFT.Concrete.Handle hash hash-cr
 open import LibraBFT.Concrete.Consensus.Types

 EventProcessor₀ : Fin #peer → EventProcessor
 EventProcessor₀ = {!!}

 author2peer : Author → Fin #peer
 author2peer = {!!}

 step' : EventProcessor → NetworkMsg
       → List (Fin #peer × NetworkMsg) × EventProcessor
 step' st m = let (acts , st') = step st m
               in (List-map (×-map author2peer id) acts , st')

 -- open import LibraBFT.Global.SystemModel #peer
 -- open WithParms NetworkMsg EventProcessor EventProcessor₀ step'
 
   
 
