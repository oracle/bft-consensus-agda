open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode

module LibraBFT.Concrete.Types where

  open import LibraBFT.Abstract.Types public

  -- Create an EpochConfig for each epoch.  This is just for testing and facilitating progress on
  -- other stuff.

  fakeAuthorsN : ℕ
  fakeAuthorsN = 4

  fakeAuthors : NodeId → Maybe (Fin fakeAuthorsN)
  fakeAuthors nid with nid <? fakeAuthorsN
  ...| yes xx = just (fromℕ≤ xx)
  ...| no  _  = nothing

  postulate
    fakeNodeIdPK : NodeId → PK
    fakePKs      : Fin fakeAuthorsN → PK
    fakePKsInj   : (x x₁ : Fin 4) (x₂ : fakePKs x ≡ fakePKs x₁) → x ≡ x₁

  fakeEC : EpochId → EpochConfig
  fakeEC eid = record {
                 epochId           = eid
               ; authorsN          = fakeAuthorsN
               ; bizF              = 1
               ; isBFT             = s≤s (s≤s (s≤s (s≤s z≤n)))
               ; seed              = 0
               ; ecInitialState    = dummyHash
               ; initialAgreedHash = dummyHash

               }

  postulate
    fakePKI : (ec : EpochConfig) → PKI ec

