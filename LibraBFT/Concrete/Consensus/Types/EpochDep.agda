open import LibraBFT.Prelude
open import LibraBFT.Hash
open import LibraBFT.Base.PKCS
open import LibraBFT.Base.Encode
open import LibraBFT.Concrete.Util.KVMap as KVMap

open import LibraBFT.Concrete.Consensus.Types

open import Optics.All

-- Semantic validitadion of the data structures in 'Consensus.Types'
-- depends directly on the epoch configuration.
module LibraBFT.Concrete.Consensus.Types.EpochDep (ec : EpochConfig) where


  -- VCM: I think this is incorrect.
  --      I can always prove all authors valid...
  record IsValidQCAuthor (_ : Author) : Set where
    field
      _ivaIdx : EpochConfig.Author ec
  open IsValidQCAuthor public

  -- Here!
  vcm-absurd : ∀{a} → IsValidQCAuthor a
  vcm-absurd = record { _ivaIdx = first-author ec }
    where
      first-author : (x : EpochConfig) → EpochConfig.Author x
      first-author (record 
         { epochId = epochId 
         ; authorsN = suc authorsN 
         ; bizF = bizF 
         ; isBFT = s≤s isBFT 
         ; seed = seed 
         ; ecInitialState = ecInitialState 
         ; initialAgreedHash = initialAgreedHash 
         ; isAuthor = isAuthor }) 
           = zero
  
  record IsValidQC (qc : QuorumCert) : Set where
    field
      _ivqcSizeOk       : QuorumSize ec ≤ length (qcVotes qc)
      _ivqcValidAuthors : All ((IsValidQCAuthor ∘ proj₁) ) (qcVotes qc)
  open IsValidQCAuthor public

  -- A block tree depends on a epoch config but works regardlesss of which
  -- epoch config we have. Moreover, this epoch config can't be changed internally
  -- to the block tree, hence, it really shouldn't be a field of the BlockTree.
  record BlockTree : Set where
    constructor mkBlockTree
    field
      _btIdToBlock               : KVMap HashValue LinkableBlock
      :btRootId                  : HashValue
      _btHighestCertifiedBlockId : HashValue
      _btHighestQuorumCert       : QuorumCert
      -- btHighestTimeoutCert      : Maybe TimeoutCertificate
      _btHighestCommitCert       : QuorumCert
      _btPendingVotes            : PendingVotes
      _btPrunedBlockIds          : List HashValue
      _btMaxPrunedBlocksInMem    : ℕ
      _btIdToQuorumCert          : KVMap HashValue (Σ QuorumCert IsValidQC)
  open BlockTree public

  -- Here, we manually construct a lens for accessing the btRoodId field.  However, we cannot use
  -- the Haskell conventional _ prefix for the field name, as Agda thinks this is a postfix operator
  -- definition.  Using : for now; just for this field while experimenting with ideas.  TODO: decide
  -- what to do and do it consistently.

  btRootId : Lens BlockTree HashValue
  btRootId = mkLens' :btRootId (λ bt fv → record bt {:btRootId = fv})

{-
  -- VCM: Lenses are not working for records with module parameterss... :(
  -- if we really want it, I can try to fix it; but given there will only be two
  -- such recods; we might be better off defining them by hand.
  -- VCM: UPDATE: won't work anyway: check comment at Types.EventProcessor
  unquoteDecl btIdToBlock   btRootId   btHighestCertifiedBlockId   btHighestQuorumCert
              btHighestCommitCert   btPendingVotes   btPrunedBlockIds
              btMaxPrunedBlocksInMem = mkLens (quote BlockTree)
             (btIdToBlock ∷ btRootId ∷ btHighestCertifiedBlockId ∷ btHighestQuorumCert ∷
              btHighestCommitCert ∷ btPendingVotes ∷ btPrunedBlockIds ∷
              btMaxPrunedBlocksInMem ∷ [])
-}

  -- This should live in BlockTree.hs.  Here to avoid circular import.
  -- This should not be used outside BlockTree.hs.
  btGetLinkableBlock : HashValue -> BlockTree -> Maybe LinkableBlock
  btGetLinkableBlock hv bt = KVMap.lookup hv (_btIdToBlock bt)

  -- This should live in BlockTree.hs.  Here to avoid circular import.
  btGetBlock : HashValue -> BlockTree -> Maybe ExecutedBlock
  btGetBlock hv bt = Maybe-map _lbExecutedBlock (btGetLinkableBlock hv bt)

  btRoot : BlockTree → ExecutedBlock
  btRoot bt with (btGetBlock (:btRootId bt)) bt | inspect (btGetBlock (:btRootId bt)) bt
  ...| just x  | _ = x
  ...| nothing | [ imp ] = ⊥-elim (assumedValid bt imp)
   where postulate
           -- VCM: Isn't this a very dangerous postulate here?
           -- I think our btRoot should return a Maybe or should receive
           -- this postulate as a parameter... 
           assumedValid : (bt : BlockTree) → btGetBlock (:btRootId bt) bt ≡ nothing → ⊥

  record BlockStore : Set where
    constructor mkBlockStore
    field
      _bsInner         : BlockTree
      -- bsStateComputer : StateComputer
      -- bsStorage       : CBPersistentStorage
  open BlockStore public
{-
  unquoteDecl bsInner = mkLens (quote BlockStore)
             (bsInner ∷ [])
-}

  bsRoot : BlockStore → ExecutedBlock
  bsRoot = btRoot ∘ _bsInner

  -- bsHighestCertifiedBlock :: GetterNoFunctor (BlockStore a) (ExecutedBlock a)
  -- bsHighestCertifiedBlock  = to (^.bsInner.btHighestCertifiedBlock)

  -- bsHighestQuorumCert :: GetterNoFunctor (BlockStore a) QuorumCert
  -- bsHighestQuorumCert  = to (^.bsInner.btHighestQuorumCert)

  -- bsHighestCommitCert :: GetterNoFunctor (BlockStore a) QuorumCert
  -- bsHighestCommitCert  = to (^.bsInner.btHighestCommitCert)

  -- bsHighestTimeoutCert :: GetterNoFunctor (BlockStore a) (Maybe TimeoutCertificate)
  -- bsHighestTimeoutCert  = to (^.bsInner.btHighestTimeoutCert)

