open import LibraBFT.Prelude
open import LibraBFT.Concrete.Consensus.Types


module LibraBFT.Concrete.OBM.Util where

{-
  maybeMP :: Monad m => m (Maybe a) -> b -> (a -> m b) -> m b
  maybeMP mma b f = mma >>= \case Nothing -> pure b; Just j -> f j
-}

  -- TODO: Go over this with Harold and/or Victor to be sure I understood the Haskell correctly and
  -- wrote the Agda correctly

  maybeMP : {a b : Set} → LBFT (Maybe a) → b → (a → LBFT b) → LBFT b
  maybeMP x b f {state₀} {acts₀}
     with x {state₀} {acts₀}
  ...| nothing , state₁ , acts₁ = b , state₁ , acts₁
  ...| just jx , state₁ , acts₁ = f jx {state₁} {acts₁}
