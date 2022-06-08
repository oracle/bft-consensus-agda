module Dijkstra.AST.Examples.Either.Bind where

open import Data.Nat
open import Dijkstra.AST.Core
open import Util.Prelude
open import Dijkstra.AST.Either ⊤
open        ASTTypes         EitherTypes
open        ASTPredTrans     EitherPT
open        ASTPredTransMono EitherPTMono

module TwoEitherBindsExample
  (en1 en2 : EitherAST ℕ)
  where

  prog : EitherAST (List ℕ)
  prog = do
    n1 ← en1
    n2 ← en2
    ASTreturn (n1 ∷ n2 ∷ [])

  ProgPost : Unit → Either ⊤ (List ℕ) → Set
  ProgPost _ (Left  l) =        l ≡ tt
  ProgPost _ (Right r) = length r ≡ 2

  progPostWP : predTrans prog (ProgPost unit) unit
  progPostWP = predTransMono prog runPost _ ⊆ₒProgPost unit PT
   where
    runPost : Post (List ℕ)
    runPost = runEitherAST prog unit ≡_

    ⊆ₒProgPost : runPost ⊆ₒ ProgPost unit
    ⊆ₒProgPost (Left  _) _                                               = refl
    ⊆ₒProgPost (Right r) Right_n1∷n2∷[]≡Right_r with runEitherAST en1 unit
    ... | (Right n1)                            with runEitherAST en2 unit
    ... | (Right n2) rewrite inj₂-injective (sym Right_n1∷n2∷[]≡Right_r) = refl

    PT : predTrans prog runPost unit
    PT = predTrans-is-weakest prog _ refl
