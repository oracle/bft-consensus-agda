open import Function
open import Data.Unit
open import Data.List as List
open import Data.Char
open import Data.Nat as ℕ
open import Data.Product
open import Data.String
open import Relation.Nullary using (Dec; yes; no)
open import Category.Functor

open import Reflection

open import Optics.Functorial

module Optics.Reflection where

 private
  tcMapM : {A B : Set} → (A → TC B) → List A → TC (List B)
  tcMapM f [] = return []
  tcMapM f (x ∷ xs) = do
    y ← f x
    ys ← tcMapM f xs
    return (y ∷ ys)

  count : ℕ → List ℕ
  count 0       = [] 
  count (suc n) = 0 ∷ List.map suc (count n)

  List-last : {A : Set} → A → List A → A
  List-last d []       = d
  List-last d (x ∷ []) = x
  List-last d (x ∷ xs) = List-last d xs

  ai : {A : Set} → A → Arg A
  ai x = arg (arg-info visible relevant) x

  record MetaLens : Set where
    constructor ml
    field
      mlName : Name
      mlType : Type
      mkDef  : Term

  -- Example call:
  -- Let:
  -- > record Test : Set where
  -- >   constructor test
  -- >   field
  -- >     firstField  : ℕ
  -- >     secondField : Maybe String
  --
  -- Then; consider the call:
  --
  -- > go Test test [x , y] 2 secondField
  --
  -- What we want to generate is:
  --
  -- 
  -- > secondField : Lens Name (Maybe String)
  -- > secondField = lens (λ { F rf f (test x y) 
  -- >                     → (RawFunctor._<$>_ rf) 
  -- >                       (λ y' → test x y') (f y) 
  -- >                     })
  --
  -- Which is captured by the MetaLens
  go : Name → Name → List String → ℕ → (Name × Arg Name) → TC MetaLens
  go rec cName vars curr (lensName , (arg _ fld)) = do
     -- Get the type of the field; in our case: Mabe String
     tyFld    ← (getType fld >>= parseTy)
     -- compute the full lens type: Lens Test (Maybe String)
     let finalTy = def (quote Lens) (ai (def rec []) ∷ ai tyFld ∷ [])
     -- compute the clause of the lens:
     return (ml lensName finalTy genTerm)
   where
     parseTy : Type → TC Type
     parseTy (pi _ (abs _ t)) = parseTy t
     parseTy (var (suc x) i)  = return (var x i)
     parseTy r                = return r

     -- We might be at field 0; but our de Bruijn index depends
     -- on the total of fields
     curr' : ℕ
     curr' = List.length vars ∸ suc curr

     testxy : Pattern
     testxy = con cName (List.map (ai ∘ var) vars)

     myabs : Term → Term
     myabs t = pat-lam (clause (ai (var "F") ∷ ai (var "rf") ∷ ai (var "f") ∷ ai testxy ∷ []) t ∷ []) []

     myvar : ℕ → List (Arg Term) → Term
     myvar n args = var (List.length vars + n) args

     RawFunctor-<$>-var2 : Term → Term → Term
     RawFunctor-<$>-var2 testxy' fy =
       let rawf = quote RawFunctor._<$>_
        in def rawf (ai (myvar 1 []) ∷ (ai testxy') ∷ (ai fy) ∷ [])

     f-varN : Term
     f-varN = myvar 0 (ai (var curr' []) ∷ [])

     xy' : List (Arg Term)
     xy' = let xs = reverse (count (List.length vars))
            in List.map (λ m → ai (var (suc+set0 m) [])) xs
       where
         suc+set0 : ℕ → ℕ
         suc+set0 m = case m ℕ.≟ curr' of
                        λ { (no _) → suc m
                          ; (yes _) → zero
                          }

     testxy' : Term
     testxy' = lam visible (abs "y'" (con cName xy'))

     -- We will now generate the RHS of second field: lens (λ { F rf ⋯ 
     genTerm : Term
     genTerm = con (quote lens) (ai (myabs (RawFunctor-<$>-var2 testxy' f-varN)) ∷ [])

  mkLensFrom : Name → Definition → List Name → TC (List MetaLens)
  mkLensFrom rec (record′ c fs) lnames = do
    let xs = count (List.length fs)
    let vars = List.map (flip Data.String.replicate 'v' ∘ suc) xs
    tcMapM (uncurry (go rec c vars)) (List.zip xs (List.zip lnames fs))
  mkLensFrom _ _ _ = typeError (strErr "Not a record" ∷ [])

  defineLens : MetaLens → TC ⊤
  defineLens (ml n ty trm) 
    = do -- typeError (nameErr n ∷ strErr "%%" ∷ termErr ty ∷ strErr "%%" ∷ termErr trm ∷ [])
         declareDef (arg (arg-info visible relevant) n) ty
         defineFun n (clause [] trm ∷ [])

 mkLens : Name → List Name → TC ⊤
 mkLens rec lenses = do
   r ← getDefinition rec
   res ← mkLensFrom rec r lenses
   tcMapM defineLens res  
   return tt
  -- usage will be: unquoteDecl = mkLens RecordName 

