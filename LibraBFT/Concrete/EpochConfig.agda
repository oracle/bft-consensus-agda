open import LibraBFT.Prelude
open import LibraBFT.BasicTypes
open import LibraBFT.Lemmas

import LibraBFT.Abstract.EpochConfig as Abstract

module LibraBFT.Concrete.EpochConfig where

  -- VCM: This is an example bridge between an Abstract.EpochConfig
  --      an a Concrete.EpochConfig. On the concrete one we have a list of 
  --      nodes that are designated authors. We have an initial state, etc...
  record EpochConfig : Set where
    field
      ecEpochId        : EpochId
      ecValidAuthors   : List NodeId
      -- MSM: Don't we need to reqiure the authors to be distinct?
      -- We claim in LibraBFT.Abstract.Records that ordering Votes
      -- by Author index ensures they are different, which would not
      -- be true if Authors were duplicated in this list.
      ecInitialState   : State
      -- ecPubKeys  : NodeId → PubKey
      -- etc
  open EpochConfig public

  private
    div3 : ℕ → ℕ
    div3 zero                = zero
    div3 (suc zero)          = zero
    div3 (suc (suc zero))    = zero
    div3 (suc (suc (suc x))) = suc (div3 x)

  -- It is only natural, then, that a Concrete.EpochConfig can 
  -- handle up to a maximum byzantine failures
  ecMaxByzantine : EpochConfig → ℕ
  -- TODO: if number of authors is less than 3 then this returns 0
  ecMaxByzantine ec = div3 (length (ecValidAuthors ec) ∸ 1)

  -- Which in turn, enables us to construct an abstract epoch config
  -- for the maximum amount of byzantine failures we can and use
  -- this one to instantiate the modules inside LibraBFT.Abstract.
  ecAbstract : (ec : EpochConfig) 
             → Abstract.EpochConfig (ecMaxByzantine ec)
  ecAbstract ec = record 
    { epochId  = ecEpochId ec 
    ; authorsN = length (ecValidAuthors ec) 
    ; isBFT    = todo
    ; seed     = todo
    } where postulate todo : ∀{a}{A : Set a} → A 

  -- A prominent example are authors. Concrete authors are an index into
  -- the abstract epoch config. When we receive a message we check that
  -- the author is in the Concrete.epochConfig.ecValidAuthors then 
  -- translate into an index of that list.
  Author : EpochConfig → Set
  Author ec = Abstract.Author (ecAbstract ec)
