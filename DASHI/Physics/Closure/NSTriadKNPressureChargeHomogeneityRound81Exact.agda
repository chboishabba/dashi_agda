module DASHI.Physics.Closure.NSTriadKNPressureChargeHomogeneityRound81Exact where

------------------------------------------------------------------------
-- ROUND81 / PRESSURE-CHARGE HOMOGENEITY AUDIT
--
-- The pressure-Hessian Fourier isometry removes Riesz-operator loss, but it
-- does NOT make the pressure charge quadratic.  The Poisson source
--
--   h = ||S||_F^2 - |omega|^2 / 2
--
-- is quadratic in the velocity gradient.  Under amplitude multiplication
-- u -> a u at one fixed periodic datum,
--
--   h -> a^2 h,
--   ||Hess p||_2^2 = ||h||_2^2 -> a^4 ||h||_2^2,
--
-- whereas the ordinary gradient dissipation scales only as a^2.
--
-- This is a homogeneity audit, not a claim that amplitude multiplication is an
-- NS solution symmetry at fixed viscosity.  It applies to any proposed
-- pointwise-in-data universal estimate intended to hold for arbitrary smooth
-- initial data.  Such an estimate cannot treat pressure-Hessian square mass as
-- an ordinary fixed-coefficient quadratic dissipation owner without some
-- additional concentration/smallness/localization structure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

square : ℚ → ℚ
square x = x * x

fourth : ℚ → ℚ
fourth x = square (square x)

scaledQuadraticDissipation : ℚ → ℚ → ℚ
scaledQuadraticDissipation amplitude baseDissipation =
  square amplitude * baseDissipation

scaledPressureHessianSquareCharge : ℚ → ℚ → ℚ
scaledPressureHessianSquareCharge amplitude basePressureCharge =
  fourth amplitude * basePressureCharge

pressureChargeHasAmplitudeDegreeFour :
  ∀ amplitude basePressureCharge →
  scaledPressureHessianSquareCharge amplitude basePressureCharge
  ≡ fourth amplitude * basePressureCharge
pressureChargeHasAmplitudeDegreeFour amplitude basePressureCharge = refl

dissipationHasAmplitudeDegreeTwo :
  ∀ amplitude baseDissipation →
  scaledQuadraticDissipation amplitude baseDissipation
  ≡ square amplitude * baseDissipation
dissipationHasAmplitudeDegreeTwo amplitude baseDissipation = refl

two : ℚ
two = 1ℚ + 1ℚ

-- If the base pressure and quadratic-dissipation charges coincide, a dyadic
-- amplitude increase makes pressure charge exactly four times the scaled
-- quadratic dissipation.  This is the cheapest exact witness of the mismatch.
dyadicPressureChargeOutgrowsQuadraticDissipationByFour :
  ∀ baseCharge →
  scaledPressureHessianSquareCharge two baseCharge
  ≡ (two * two) * scaledQuadraticDissipation two baseCharge
dyadicPressureChargeOutgrowsQuadraticDissipationByFour baseCharge =
  solve (baseCharge ∷ [])

-- More generally, if the base pressure charge is coefficient*C times the base
-- dissipation, the coefficient after amplitude scaling acquires an additional
-- factor a^2.
scaledPressureCoefficientGainsAmplitudeSquare :
  ∀ amplitude coefficient baseDissipation →
  scaledPressureHessianSquareCharge
      amplitude (coefficient * baseDissipation)
  ≡ (square amplitude * coefficient)
      * scaledQuadraticDissipation amplitude baseDissipation
scaledPressureCoefficientGainsAmplitudeSquare amplitude coefficient baseDissipation =
  solve (amplitude ∷ coefficient ∷ baseDissipation ∷ [])

round81PressureHessianL2OperatorCausesNoExtraDerivativeLoss : Bool
round81PressureHessianL2OperatorCausesNoExtraDerivativeLoss = true

round81PressureHessianSquareChargeHasQuadraticDissipationHomogeneity : Bool
round81PressureHessianSquareChargeHasQuadraticDissipationHomogeneity = false

round81PressureChargeNeedsAdditionalStructureForQuadraticFunding : Bool
round81PressureChargeNeedsAdditionalStructureForQuadraticFunding = true

round81PressureHessianSquareChargeHasQuadraticDissipationHomogeneityIsFalse :
  round81PressureHessianSquareChargeHasQuadraticDissipationHomogeneity ≡ false
round81PressureHessianSquareChargeHasQuadraticDissipationHomogeneityIsFalse = refl
