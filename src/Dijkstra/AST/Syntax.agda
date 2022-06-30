{- Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.

   Copyright (c) 2022, Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}

module Dijkstra.AST.Syntax where

open import FunctorApplicativeMonad public
open import Dijkstra.Syntax         public

instance
  open import Dijkstra.AST.Core

  MonadAST : ∀ {OP : ASTOps} → Monad (AST OP)
  Monad.return MonadAST = ASTreturn
  Monad._>>=_  MonadAST = ASTbind


