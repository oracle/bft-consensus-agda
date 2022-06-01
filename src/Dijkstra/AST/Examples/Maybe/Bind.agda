module Dijkstra.AST.Examples.Maybe.Bind where

open import Data.Nat renaming (ℕ to Nat)
open import Dijkstra.AST.Core
open import Dijkstra.AST.Maybe
open        Syntax
open        ASTTypes     MaybeTypes
open        ASTPredTrans MaybePT
open        ASTOpSem     MaybeOpSem
open import Haskell.Prelude
open import Util.Prelude

prog : (mn1 mn2 : MaybeD Nat) -> MaybeD (List Nat)
prog mn1 mn2 = do
  n1 <- mn1
  n2 <- mn2
  return (n1 ∷ n2 ∷ [])

ProgPost : Unit -> Maybe (List Nat) -> Set
ProgPost _  nothing = ⊤
ProgPost _ (just l) = length l ≡ 2

progPostWP : ∀ mn1 mn2
          -> ASTPredTrans.predTrans MaybePT (prog mn1 mn2) (ProgPost unit) unit
progPostWP mn1 mn2 =
  ASTPredTransMono.predTransMono MaybePTMono
    (prog mn1 mn2) (λ o → runMaybe (prog mn1 mn2) unit ≡ o) _ ⊆ₒProgPost unit PT
 where
  ⊆ₒProgPost : (λ o → runMaybe (prog mn1 mn2) unit ≡ o) ⊆ₒ ProgPost unit
  ⊆ₒProgPost nothing _ = tt
  ⊆ₒProgPost (just l) just_n1∷n2∷[]≡just_l with runMaybe mn1 unit
  ... | just n1                           with runMaybe mn2 unit
  ... | just n2 rewrite just-injective (sym just_n1∷n2∷[]≡just_l) = refl

  PT : predTrans (prog mn1 mn2) (λ o → runMaybe (prog mn1 mn2) unit ≡ o) unit
  PT = {!!}

progPost : ∀ mn1 mn2  -> ProgPost unit (runMaybe (prog mn1 mn2) unit)
progPost mn1 mn2 =
  ASTSufficientPT.sufficient MaybeSuf (prog mn1 mn2) (ProgPost unit) unit (progPostWP mn1 mn2)

