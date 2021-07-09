{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2020, 2021, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

open import LibraBFT.ImplShared.Base.Types

open import LibraBFT.Abstract.Types.EpochConfig UID NodeId
open import LibraBFT.Concrete.System
open import LibraBFT.Concrete.System.Parameters
open import LibraBFT.ImplFake.Handle
open import LibraBFT.ImplFake.Handle.Properties
open import LibraBFT.ImplShared.Consensus.Types
open import LibraBFT.Prelude

import      LibraBFT.Concrete.Properties.PreferredRound FakeInitAndHandlers as PR
open        ParamsWithInitAndHandlers FakeInitAndHandlers
open import LibraBFT.Yasm.Yasm ℓ-RoundManager ℓ-VSFP ConcSysParms FakeInitAndHandlers
                               PeerCanSignForPK (λ {st} {part} {pk} → PeerCanSignForPK-stable {st} {part} {pk})
open        Structural impl-sps-avp

open import LibraBFT.Concrete.Obligations

-- In this module, we (will) prove the implementation obligation for the PreferredRound rule.

module LibraBFT.ImplFake.Properties.PreferredRound (𝓔 : EpochConfig) where

  postulate  -- TODO-3 : prove.  Note that this is a substantial
             -- undertaking that should not be started before we have
             -- a proof for the similar-but-much-simpler VotesOnce
             -- property, and also not before we have an
             -- implementation (perhaps some incremental extension of
             -- our current fake/simple implementaion) that we can
             -- reasonably hope actually ensures the property!
    pr₁ : PR.ImplObligation₁ 𝓔

  --TODO-2: This proof is highly redundant with vo₁, some refactoring may be in order
  pr₂ : PR.ImplObligation₂ 𝓔
  pr₂ {pk = pk} {st} r stMsg@(step-msg {_ , P m} m∈pool psI) pkH v⊂m m∈outs sig ¬gen vnew _ v'⊂m' m'∈outs sig' ¬gen' v'new _ refl vround< refl refl c2
     with m∈outs | m'∈outs
  ...| here refl | here refl
     with v⊂m                          | v'⊂m'
  ...| vote∈vm                         | vote∈vm = ⊥-elim (<⇒≢ vround< refl) -- Only one VoteMsg is
                                                                             -- sent, so the votes
                                                                             -- must be the same,
                                                                             -- contradicting
                                                                             -- vround<
  ...| vote∈vm                         | vote∈qc vs∈qc' v≈rbld' (inV qc∈m')
       rewrite cong _vSignature v≈rbld'
       = let qc∈rm' = VoteMsgQCsFromRoundManager r stMsg pkH v'⊂m' (here refl) qc∈m'
         in ⊥-elim (v'new (qcVotesSentB4 r psI qc∈rm' vs∈qc' ¬gen'))
  ...| vote∈qc vs∈qc v≈rbld (inV qc∈m) | _
       rewrite cong _vSignature v≈rbld
       = let qc∈rm = VoteMsgQCsFromRoundManager r stMsg pkH v⊂m (here refl) qc∈m
         in ⊥-elim (vnew (qcVotesSentB4 r psI qc∈rm vs∈qc ¬gen))
