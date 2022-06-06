module Dijkstra.AST.Examples.Either.Bind where

open import Data.Nat    renaming (ℕ to Nat)
open import Dijkstra.AST.Core
open import Util.Prelude     hiding (return)
open import Dijkstra.AST.Either ⊤
open        Syntax
open        SyntaxExt
open        ASTTypes         EitherTypes
open        ASTPredTrans     EitherPT
open        ASTPredTransMono EitherPTMono
open        ASTOpSem         EitherOpSem
open import Haskell.Prelude  hiding (return)

right-injective : ∀ {A B : Set} {x y} → (Either A B ∋ Right x) ≡ Right y → x ≡ y
right-injective refl = refl

module TwoEitherBindsExample
  (en1 en2 : EitherAST Nat)
  where

  prog : EitherAST (List Nat)
  prog = do
    n1 <- en1
    n2 <- en2
    ASTreturn (n1 ∷ n2 ∷ [])

  ProgPost : Unit -> Either ⊤ (List Nat) -> Set
  ProgPost _ (Left  l) =        l ≡ tt
  ProgPost _ (Right r) = length r ≡ 2

  progPostWP : predTrans prog (ProgPost unit) unit
  progPostWP =
    predTransMono
      prog (λ o → runEither prog unit ≡ o) _ ⊆ₒProgPost unit PT
   where
    ⊆ₒProgPost : (λ o → runEither prog unit ≡ o) ⊆ₒ ProgPost unit
    ⊆ₒProgPost (Left  _) _                                                = refl
    ⊆ₒProgPost (Right r) Right_n1∷n2∷[]≡Right_r with runEither en1 unit
    ... | (Right n1)                            with runEither en2 unit
    ... | (Right n2) rewrite right-injective (sym Right_n1∷n2∷[]≡Right_r) = refl

    PT : predTrans prog (λ o → runEither prog unit ≡ o) unit
    PT = predTrans-is-weakest prog _ refl
