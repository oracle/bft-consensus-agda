module Dijkstra.AST.Examples.SEFM-Intro (Ev Wr St : Set) where

open import Data.Maybe                  using (maybe)
open import Data.Product                using (_×_ ; _,_)
open import Dijkstra.AST.Core
open import Dijkstra.AST.RWS Ev Wr St
open RWSBase.RWSCmd
open import Function                    using (case_of_)
open import Haskell.Prelude             hiding (maybe)
open import Level                       as Level
open import Relation.Binary.PropositionalEquality

prog : (St → Maybe Wr) → RWSAST Unit
prog f = pass inner
 where inner : RWSAST (Unit × (List Wr → List Wr))
       inner = do
         m ← gets f
         maybe (λ w → do
                 tell (w ∷ [])
                 return (unit , λ _ → []))
               (return (unit , λ x → x ++ x))
               m

progSyntax : (St → Maybe Wr) → RWSAST Unit
progSyntax f = pass $ do
  m <- gets f
  case m of λ where
    (just w) → do
      tell (w ∷ [])
      return (unit , λ _ → [])
    nothing  →
      return (unit , λ x → x ++ x)

progAST : (St → Maybe Wr) → RWSAST Unit
progAST f =
  ASTop (Left RWSpass)
        (λ { (Level.lift unit)
          → ASTbind (ASTop (Left (RWSgets f)) (λ ()))
                    (maybe (λ w → ASTbind
                                  (ASTop (Left (RWStell (w ∷ []) refl)) (λ ()))
                                  (λ _ → ASTreturn (unit , (λ _ → []))))
                           (ASTreturn (unit , (λ x → x ++ x))))
           })

------------------------------------------------------------------------------

-- Note: the below all work when all instances of 'prog' are replaced by 'progSyntax' or 'progAST'.

ProgPost : (Ev × St) → (Unit × St × List Wr) → Set
ProgPost (_ , s1) (_ , s2 , o) = s1 ≡ s2 × 0 ≡ length o

progPost : ∀ f i → ProgPost i (runRWSAST (prog f) i)
progPost f (_ , s) with f s
... | nothing = refl , refl
... | just _  = refl , refl

progPostWP  : ∀ f i → predTrans (prog f) (ProgPost i) i
progPostWP _ (_ , _) nothing  _ _ r≡[]        rewrite r≡[] = refl , refl
progPostWP _ (_ , _) (just _) _ _ _    _ r≡[] rewrite r≡[] = refl , refl

progPost2 : ∀ f i → ProgPost i (runRWSAST (prog f) i)
progPost2 f i = sufficient (prog f) (ProgPost i) i (progPostWP f i)

