open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.BasicTypes
open import LibraBFT.Lemmas

module LibraBFT.Abstract.BFT {f : ℕ} (ec : EpochConfig f) where

 open import LibraBFT.Abstract.Records ec
 
 postulate
   lemmaB1 : (q₁ : QC)(q₂ : QC) 
           → ∃[ a ] (a ∈QC q₁ × a ∈QC q₂ × Honest {ec = ec} a)


