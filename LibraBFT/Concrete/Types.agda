open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode

module LibraBFT.Concrete.Types where

  open import LibraBFT.Abstract.Types public hiding (Author)

  -- Create an EpochConfig for each epoch.  This is just for testing and facilitating progress on
  -- other stuff.

  Author : Set
  Author = NodeId

  fakeAuthorsN : ℕ
  fakeAuthorsN = 4

  fakeAuthors : NodeId → Maybe (Fin fakeAuthorsN)
  fakeAuthors nid with nid <? fakeAuthorsN
  ...| yes xx = just (fromℕ≤ xx)
  ...| no  _  = nothing

  -- We want to associate PKs with all participants (not just those of the current epoch).  This is
  -- so we can verify signatures on fraudulent messages pretending to be authors of an epoch for
  -- accountability reasons, and also because that's what libra does.
  record PKI : Set where
    field
      pkAuthor : NodeId → PK
      pkInj    : ∀ (n₁ n₂ : NodeId)          -- Authors must have distinct public keys, otherwise a
               → pkAuthor n₁ ≡ pkAuthor n₂   -- dishonest author can potentially impersonate an honest
               → n₁ ≡ n₂                     -- author.
  open PKI public

  fakeEC : EpochId → EpochConfig
  fakeEC eid = record {
                 epochId           = eid
               ; authorsN          = fakeAuthorsN
               ; bizF              = 1
               ; isBFT             = s≤s (s≤s (s≤s (s≤s z≤n)))
               ; seed              = 0
               ; ecInitialState    = dummyHash
               ; initialAgreedHash = dummyHash
               ; isAuthor          = fakeAuthors

               }

