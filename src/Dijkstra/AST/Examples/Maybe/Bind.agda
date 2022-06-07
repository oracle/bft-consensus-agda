open import Data.Nat renaming (ℕ to Nat)
open import Dijkstra.AST.Core
open import Dijkstra.AST.Maybe
open        MaybeSyntax
open        ASTOpSem         MaybeOpSem
open        ASTPredTrans     MaybePT
open        ASTPredTransMono MaybePTMono
open        ASTSufficientPT  MaybeSuf
open        ASTTypes         MaybeTypes
open import Haskell.Prelude
open import Util.Prelude

module Dijkstra.AST.Examples.Maybe.Bind (mn1 mn2 : MaybeD Nat) where

module OneMaybeBindExample where
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

  -- Here is the property we want to prove
  progPostWP : predTrans prog ProgPost unit
  -- This long-winded proof was helpful in understanding how to make the proof work
  -- Agda knows the Goal postcondition because it knows that prog is a bind, and knows the rest of
  -- the program.  To help us understand what it is that Agda figures out to enable putting _ for
  -- the goal argument below, we define Goal below, and we can replace _ by Goal and see that it's
  -- right.
  progPostWP = predTransMono mn1 mn1Post _ {- Goal -} mn1Post⇒Goal unit PT
    where

    Goal : Post Nat
    Goal x = -- The following goal is determined by:
             -- bindPT (λ x → predTrans (Monad.return MonadAST (x ∷ []))) unit ProgPost
             -- because prog is an AST-bind at the top level
           ∀ r → r ≡ x → MaybebindPost (λ x → predTrans (Monad.return MonadAST (x ∷ []))) ProgPost r

    PT : _
    PT with runAST mn1 unit | inspect (runAST mn1) unit
    ... | nothing | [ R ] = predTrans-is-weakest mn1 mn1Post (subst mn1Post (sym R) tt)
    ... | just x  | [ R ] = predTrans-is-weakest mn1 _       (subst mn1Post (sym R) R)

    mn1Post⇒Goal : _
    mn1Post⇒Goal nothing   mn1Postnothing .nothing   refl = tt
    mn1Post⇒Goal (just x₁) mn1Postjust    .(just x₁) refl = refl

  -- Here is an alternative proof showing how maybePTLemma makes it easy for the user to provide the
  -- needed cases for a proof about a bind
  progPostWP2 : predTrans prog ProgPost unit
  progPostWP2 = maybePTBindLemma prog refl nothingCase justCase
    where
    nothingCase : _
    nothingCase _ = tt
    justCase : _
    justCase _ _  = refl

module TwoMaybeBindsExample where

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

  -- A nicer proof using maybePTBindLemma (twice)
  progPostWP2 : predTrans prog (ProgPost unit) unit
  progPostWP2 = maybePTBindLemma prog refl nothingCase justCase
    where

    nothingCase : _
    nothingCase _ = tt

    justCase : _
    justCase x _ = let f = bindCont prog refl x
                    in sufficient f
                         (ProgPost unit)
                         unit
                         (maybePTBindLemma f refl (const tt) (λ x2 rm≡j → refl))

  progPost : ProgPost unit (runMaybe prog unit)
  progPost =
    sufficient prog (ProgPost unit) unit progPostWP

