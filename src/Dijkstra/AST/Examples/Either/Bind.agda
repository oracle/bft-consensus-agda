module Dijkstra.AST.Examples.Either.Bind where

open import Dijkstra.AST.Prelude

module TwoEitherBindsExample where
  open import Dijkstra.AST.Either ⊤
  open        EitherBase
  open  import Data.Nat

  module _ (en1 en2 : EitherAST ℕ) where

    prog : EitherAST (List ℕ)
    prog = do
      n1 ← en1
      n2 ← en2
      return (n1 ∷ n2 ∷ [])

    ProgPost : Unit → Either ⊤ (List ℕ) → Set
    ProgPost _ (left  l) =        l ≡ tt
    ProgPost _ (right r) = length r ≡ 2

    progPostWP : predTrans prog (ProgPost unit) unit
    progPostWP = predTransMono prog runPost _ ⊆ₒProgPost unit PT1
     where
      runPost : Post (List ℕ)
      runPost = runEitherAST prog unit ≡_

      ⊆ₒProgPost : runPost ⊆ₒ ProgPost unit
      ⊆ₒProgPost (left  _) _                                               = refl
      ⊆ₒProgPost (right r) Right_n1∷n2∷[]≡Right_r with runEitherAST en1 unit
      ... | (right n1)                            with runEitherAST en2 unit
      ... | (right n2) rewrite inj₂-injective (sym Right_n1∷n2∷[]≡Right_r) = refl

      PT1 : predTrans prog runPost unit
      PT1 = necessary prog _ unit refl
