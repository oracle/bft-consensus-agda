{-# OPTIONS --allow-unsolved-metas #-}
open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Concrete.Util.KVMap as KVMap

open import Optics.All

open import Data.String using (String)

-- Defines all the types we need. In terms of exported names,
-- this is very close to the Haskell 'LBFT.Consensus.Types'.
--
-- One important trick here is that the EventProcessor ties
-- the knot between the types that /define/ the EpochConfig
-- and the types that use the /EpochConfig/. The advantage of
-- doing this separation can be seen in OBM.Util.liftEC, where we
-- define a lifting of a function that does not change the
-- bits that define the epoch config into the whole state.
-- This enables a more elegant approach for defining functions
-- as we can see in ChainedBFT.BlockStorage.BlockTree.pathFromRootM, for example,
-- where we explicitely mention that function /does not/ change
-- the parts of the state responsible for defining the epoch config.
module LibraBFT.Concrete.Consensus.Types where
  
  open import LibraBFT.Concrete.Consensus.Types.EpochIndep public
  open import LibraBFT.Concrete.Consensus.Types.EpochDep   public

  -- The parts of the state of a replica that are used to
  -- define the EpochConfig are the SafetyRules and ValidatorVerifier:
  record EventProcessorEC : Set where
    constructor mkEventProcessorPreEC
    field
      ₋epSafetyRules  : SafetyRules
      ₋epValidators   : ValidatorVerifier
  open EventProcessorEC public
  unquoteDecl epSafetyRules epValidators = mkLens (quote EventProcessorEC)
    (epSafetyRules ∷ epValidators ∷ [])

  -- Naturally, we need to have enough authors to withstand
  -- whatever number of bizantine failures we wish to withstand.
  -- We enforce this with a predicate over 'EventProcessorEC'.
  EventProcessorEC-correct : EventProcessorEC → Set
  EventProcessorEC-correct epec = 
    let numAuthors = kvm-size (epec ^∙ epValidators ∙ vvAddressToValidatorInfo)
        qsize      = epec ^∙ epValidators ∙ vvQuorumVotingPower
        bizF       = numAuthors ∸ qsize
     in suc (3 * bizF) ≤ numAuthors 

  -- Given a well-formed set of definitions that defines an EpochConfig,
  -- α-EC will compute this epoch config by abstracting away the unecessary
  -- pieces from EventProcessorEC.
  α-EC : Σ EventProcessorEC EventProcessorEC-correct → Meta EpochConfig
  α-EC (epec , ok) = 
    let numAuthors = kvm-size (epec ^∙ epValidators ∙ vvAddressToValidatorInfo)
        qsize      = epec ^∙ epValidators ∙ vvQuorumVotingPower
        bizF       = numAuthors ∸ qsize
     in meta (mkEpochConfig 
                (epec ^∙ epSafetyRules ∙ srPersistentStorage ∙ psEpoch) 
                numAuthors
                bizF 
                ok 
                0   -- TODO: remove this 'seed' field; not used anywhere
                dummyHash 
                dummyHash 
                {!!}) -- TODO: A-ha! I see why you extracted the list from 
                      --  the validators now... will leave as a todo
                      --  as I think the internals of EpochConfig are
                      --  still volatile and this is not priority

  -- Finally, the EventProcessor is split in two pieces: those
  -- that are used to make an epoch config versus those that 
  -- use an epoch config.
  record EventProcessor : Set where
    constructor mkEventProcessor
    field
      ₋epEC           : EventProcessorEC 
      ₋epEC-correct   : EventProcessorEC-correct ₋epEC
      ₋epWithEC       : EventProcessorWithEC (α-EC (₋epEC , ₋epEC-correct))
     -- VCM: I think that if we want to add pieces that neither contribute
     -- to the construction of the EC nor need one, they should come
     -- in EventProcessor directly
  open EventProcessor public

  ------------------
  -- fakeEC below --
  ------------------

  -- VCM: This fakeAuthors and fakeEC stuff should really move somewhere
  -- else eventually, no?
  -- MSM: Yes, it is just for providing values of the appropropriate type while develop
  -- pieces that depend on them.  Maybe they will go away, or just become part of tests.

  -- Create an EpochConfig for each epoch.  This is just for testing and facilitating progress on
  -- other stuff.

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

  -- This is a placeholder for command type.  I haven't bothered making everything parameterized for
  -- this.  Maybe we shouldn't bother at all?

