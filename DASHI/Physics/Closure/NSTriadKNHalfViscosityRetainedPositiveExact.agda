module DASHI.Physics.Closure.NSTriadKNHalfViscosityRetainedPositiveExact where

------------------------------------------------------------------------
-- PERIODIC B / S4: HALF-VISCOSITY ABSORPTION LEAVES POSITIVE VISCOSITY
--
-- The literal critical-energy convention fixed in S0 has viscous coefficient
--
--   2 * nu.
--
-- Therefore formulate S2 with absorbed coefficient exactly nu.  The retained
-- coefficient is then
--
--   (2 * nu) - nu = nu,
--
-- so positivity is inherited directly from the physical viscosity receipt.
-- S4 is not an independent analytic theorem once S2 hits this natural budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _-_; Positive)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as R104

two : ℚ
two = 1ℚ + 1ℚ

halfViscositySlice :
  (nu terminal initial dissipation production remainder : ℚ) →
  terminal + (two * nu) * dissipation
    Data.Rational.Base.≤ initial + production →
  production Data.Rational.Base.≤ nu * dissipation + remainder →
  R104.IntegratedSignedCriticalSlice
halfViscositySlice
    nu terminal initial dissipation production remainder
    energy productionBound =
  R104.integrated-signed-critical-slice
    initial
    terminal
    dissipation
    production
    remainder
    (two * nu)
    nu
    energy
    productionBound

retainedHalfViscosityExact :
  (nu terminal initial dissipation production remainder : ℚ)
  (energy :
    terminal + (two * nu) * dissipation
      Data.Rational.Base.≤ initial + production)
  (productionBound :
    production Data.Rational.Base.≤ nu * dissipation + remainder) →
  R104.retainedViscosity
    (halfViscositySlice
      nu terminal initial dissipation production remainder
      energy productionBound)
  ≡ nu
retainedHalfViscosityExact nu terminal initial dissipation production remainder
    energy productionBound =
  solve (nu ∷ [])

halfViscosityRetainedPositive :
  (nu terminal initial dissipation production remainder : ℚ)
  (nuPositive : Positive nu)
  (energy :
    terminal + (two * nu) * dissipation
      Data.Rational.Base.≤ initial + production)
  (productionBound :
    production Data.Rational.Base.≤ nu * dissipation + remainder) →
  Positive
    (R104.retainedViscosity
      (halfViscositySlice
        nu terminal initial dissipation production remainder
        energy productionBound))
halfViscosityRetainedPositive
    nu terminal initial dissipation production remainder
    nuPositive energy productionBound =
  subst Positive
    (Data.Rational.Properties.≡⇒≃
      (Relation.Binary.PropositionalEquality.sym
        (retainedHalfViscosityExact
          nu terminal initial dissipation production remainder
          energy productionBound)))
    nuPositive

s4ClosedForHalfViscosityAbsorption : Bool
s4ClosedForHalfViscosityAbsorption = true

s4RequiresIndependentEstimateBeyondS2 : Bool
s4RequiresIndependentEstimateBeyondS2 = false

s2RequiredAbsorbedCoefficientIsPhysicalViscosity : Bool
s2RequiredAbsorbedCoefficientIsPhysicalViscosity = true

clayPromotion : Bool
clayPromotion = false

s4ClosedForHalfViscosityAbsorptionIsTrue :
  s4ClosedForHalfViscosityAbsorption ≡ true
s4ClosedForHalfViscosityAbsorptionIsTrue = refl

s4RequiresIndependentEstimateBeyondS2IsFalse :
  s4RequiresIndependentEstimateBeyondS2 ≡ false
s4RequiresIndependentEstimateBeyondS2IsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
