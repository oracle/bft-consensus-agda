{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Data.Nat
open import Data.Maybe
open import Data.Char
open import Data.String
open import Data.List hiding (product)
open import Relation.Binary.PropositionalEquality

open import Optics.All

module Optics.Example where

 -- First we declare a record; which must be EXACTLY
 -- like the record 'Person' below.
 -- that is; must contain a constructor and
 -- a number of /simple/ fields (of type Set; no proofs please!)
 record Person : Set where
   constructor person
   field
     pName : String
     pAge  : ℕ

 -- Then, we do some template agda:
 -- Yes,I know it looks weird; but it says:
 -- Put 'pName' and 'pAge' into scope as
 -- new identifiers; and run the metacomputation mkLens
 -- passing this newly created identifiers; the mkLens
 -- will then bind these identifiers to their respective
 -- generated lenses for the record Person
 --
 -- IMPORTANT: Note how I did NOT /open Person/; otherwise, we'd
 -- have to give different names to the lenses.
 --
 -- IMPORTANT: the list of names passed to unquoteDecl must come
 -- in the same order as the fields of Person.
 unquoteDecl pName pAge = mkLens (quote Person) (pName ∷ pAge ∷ [])

 -- Ok; lets do more recors for fun
 record Store : Set where
   constructor store
   field
     sId      : ℕ
     sManager : Person
 unquoteDecl sId sManager = mkLens (quote Store) (sId ∷ sManager ∷ [])

 record Product : Set where
   constructor product
   field
     pId    : ℕ
     pTag   : String
     pStore : Store

 unquoteDecl pId pTag pStore = mkLens (quote Product)
   (pId ∷ pTag ∷ pStore ∷ [])

 -- Let's now do a simple example:

 mary : Person
 mary = person "Mary" 41

 compilers-from-mary : Store
 compilers-from-mary = store 0 mary

 ghc : Product
 ghc = product 13 "v8.0.0" compilers-from-mary

 -- Now say mary turns 42 years old;

 ghc-from-older-mary : Product
 ghc-from-older-mary = ghc [ pStore ∙ sManager ∙ pAge := 42 ]

 same-ghc-from-mary : Product
 same-ghc-from-mary = ghc [ pStore ∙ sManager ∙ pAge %~ suc ]

 all-is-fine : ghc-from-older-mary ≡ same-ghc-from-mary
 all-is-fine = refl

 mary's-age-was-updated : ghc-from-older-mary ^∙ pStore ∙ sManager ∙ pAge ≡ 42
 mary's-age-was-updated = refl
