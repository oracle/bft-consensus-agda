module Dijkstra.AST.Examples.Maybe.Bind where

open import Data.Nat renaming (ℕ to Nat)
open import Dijkstra.AST.Core
open import Dijkstra.AST.Maybe
open        Syntax
open        ASTTypes         MaybeTypes
open        ASTPredTrans     MaybePT
open        ASTPredTransMono MaybePTMono
open        ASTOpSem         MaybeOpSem
open import Haskell.Prelude
open import Util.Prelude

module _ (mn1 mn2 : MaybeD Nat) where

  module Simpler where
    prog : MaybeD (List Nat)
    prog = do
      n1 <- mn1
      return (n1 ∷ [])

    ProgPost : Maybe (List Nat) -> Set
    ProgPost nothing = ⊤
    ProgPost (just l) = length l ≡ 1

    mn1Post : Post Nat
    mn1Post nothing = ⊤
    mn1Post (just n) = runMaybe mn1 unit ≡ just n

    progPostWP : predTrans prog ProgPost unit
    progPostWP = predTransMono mn1 mn1Post _ zz unit yy
      where

      yy : _
      yy with runAST mn1 unit | inspect (runAST mn1) unit
      ... | nothing | [ R ] = predTrans-is-weakest mn1 mn1Post (subst mn1Post (sym R) tt)
      ... | just x  | [ R ] = predTrans-is-weakest mn1 _       (subst mn1Post (sym R) R)

      zz : _
      zz nothing x .nothing refl     = tt
      zz (just x₁) x .(just x₁) refl = refl

  prog : MaybeD (List Nat)
  prog = do
    n1 <- mn1
    n2 <- mn2
    return (n1 ∷ n2 ∷ [])

  ProgPost : Unit -> Maybe (List Nat) -> Set
  ProgPost _  nothing = ⊤
  ProgPost _ (just l) = length l ≡ 2

  progPostWP : predTrans prog (ProgPost unit) unit
  progPostWP =
    predTransMono
      prog (λ o → runMaybe prog unit ≡ o) _ ⊆ₒProgPost unit PT
   where
    ⊆ₒProgPost : (λ o → runMaybe prog unit ≡ o) ⊆ₒ ProgPost unit
    ⊆ₒProgPost nothing _ = tt
    ⊆ₒProgPost (just l) just_n1∷n2∷[]≡just_l with runMaybe mn1 unit
    ... | just n1                           with runMaybe mn2 unit
    ... | just n2 rewrite just-injective (sym just_n1∷n2∷[]≡just_l) = refl

    PT : predTrans prog (λ o → runMaybe prog unit ≡ o) unit
    PT = predTrans-is-weakest prog _ refl

  progPost : ProgPost unit (runMaybe prog unit)
  progPost =
    ASTSufficientPT.sufficient MaybeSuf prog (ProgPost unit) unit progPostWP

