module DASHI.Arithmetic.VpAddUnequal where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

open import MonsterOntos using (SSP; toNat)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; alphaAt
  ; betaAt
  ; gammaAt
  ; valuationFuel
  )
open import DASHI.Arithmetic.NatBoolEquality using
  ( natEq
  ; natEq-false⇒neq
  )
open import DASHI.Arithmetic.VpDepth using
  ( minNat
  ; vp-depth-add-min-unequal
  )

------------------------------------------------------------------------
-- Core local valuation theorem surface for the bounded depth valuation.
--
-- The bridge asks the theorem in terms of the tracked `SSP` carrier and
-- the local `alpha/beta/gamma` projections. The arithmetic depth theorem
-- stays isolated in `VpDepth`, so this module only specializes it.

vp-add-min-unequal :
  ∀ p x y →
  natEq (alphaAt p x y) (betaAt p x y) ≡ false →
  gammaAt p x y ≡ minNat (alphaAt p x y) (betaAt p x y)
vp-add-min-unequal p x y wallFalse =
  vp-depth-add-min-unequal
    valuationFuel
    (toNat p)
    x
    y
    (natEq-false⇒neq (alphaAt p x y) (betaAt p x y) wallFalse)
