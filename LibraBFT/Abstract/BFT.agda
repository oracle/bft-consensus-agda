open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Lemmas
open import LibraBFT.Abstract.Types

module LibraBFT.Abstract.BFT (ec : EpochConfig) (UID : Set) where

 open import LibraBFT.Abstract.Records ec UID
 
 -- TODO: Prove the BFT assumption. Feels like its just arithmetic,
 -- but these are famous last words after the skiplog stuff, huh? :)

 -- The BFT Assumption states that the voting power of 
 -- honest authors overpower the voting power of dishonest
 -- authors. 
 --
 -- We must not inspect who is honest and who is not
 -- We will use a postulate and produce values of said type using
 -- other postulates that must be carefully checked by hand.
 postulate
   Honest : Author ec → Set

 -- A classical result tells us that in any two quorums,
 -- there exists an honest author. In Agda, we use said result
 -- as the only way of constructing an honest node.

 -- MSM: TODO This should really be about sets of authors, not about QCs.  (Classical results don't
 -- know or say anything about QCs.)  We should postulate a more general property and then prove
 -- this from it.

 postulate
   lemmaB1 : (q₁ : QC)(q₂ : QC) 
           → ∃[ a ] (a ∈QC q₁ × a ∈QC q₂ × Honest a)


