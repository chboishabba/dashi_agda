module DASHI.Physics.Closure.NSTriadKNCriticalConeHeatExponentDiagnosticRound305Exact where

------------------------------------------------------------------------
-- ROUND305 / HEAT-RESOLVENT EXPONENT DIAGNOSTIC ON THE R236 CRITICAL CONE
--
-- BIDI question from R301:
--   does the Laplace/heat factor alone make the critical-cone Schur budgets
--   summable, or is an additional signed/null/commutator gain still required?
--
-- At the dyadic-power level one parabolic heat/resolvent payment contributes
-- exactly two powers of the high shell.  This is the same exponent already
-- consumed by the H1/dissipation payment in R234/R235.  Consequently:
--
--   FL shoulder residual = 3 l - 2 m,
--   HH shoulder residual = 5 j - 4 m.
--
-- These are positive precisely on the respective critical shoulders.  On the
-- comparable ray j=m they both equal +m.  Thus heat factorization is valuable
-- for positivity and pair factorization, but HEAT ALONE DOES NOT CLOSE R301.
--
-- This is exponent arithmetic only.  It does not assert a continuum heat
-- kernel theorem or a physical Schur estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
import Data.Rational.Base as ℚ
open ℚ using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNDeepFarLowCriticalShoulderRound234Exact as R234
import DASHI.Physics.Closure.NSTriadKNDeepHHNullCriticalShoulderRound235Exact as R235
import DASHI.Physics.Closure.NSTriadKNParabolicCriticalFrequencyConeRound236Exact as R236

one two three four five : ℚ
one = 1ℚ
two = one + one
three = two + one
four = two + two
five = four + one

-- One parabolic heat/resolvent denominator at a high shell m contributes the
-- same dyadic exponent 2m as one H1/dissipation payment.
parabolicHeatPaymentExponent : ℚ → ℚ
parabolicHeatPaymentExponent highShell = two * highShell

farLowHeatResidualExponent : ℚ → ℚ → ℚ
farLowHeatResidualExponent lowShell highShell =
  R234.bernsteinSquaredExponent lowShell
  - parabolicHeatPaymentExponent highShell

farLowHeatResidualIsRound234ShoulderExcess :
  (low high : ℚ) →
  farLowHeatResidualExponent low high
  ≡ R234.criticalShoulderExcess low high
farLowHeatResidualIsRound234ShoulderExcess low high =
  solve (low ∷ high ∷ [])

hhHeatResidualExponent : ℚ → ℚ → ℚ
hhHeatResidualExponent outputShell highShell =
  R235.hhSquaredSpatialExponent outputShell highShell
  - parabolicHeatPaymentExponent highShell

hhHeatResidualIsRound235ShoulderExcess :
  (output high : ℚ) →
  hhHeatResidualExponent output high
  ≡ R235.hhResidualSquaredExponent output high
hhHeatResidualIsRound235ShoulderExcess output high =
  solve (output ∷ high ∷ [])

-- On the comparable ray all shell labels coincide.  The remaining exponent is
-- positive: heat alone leaves one full dyadic power.
farLowComparableRayResidual :
  (m : ℚ) → farLowHeatResidualExponent m m ≡ m
farLowComparableRayResidual m = solve (m ∷ [])

hhComparableRayResidual :
  (m : ℚ) → hhHeatResidualExponent m m ≡ m
hhComparableRayResidual m = solve (m ∷ [])

-- The R236 residual coordinates are literally the same diagnostic quantities.
farLowHeatResidualMatchesR236 :
  (low high : ℚ) →
  farLowHeatResidualExponent low high
  ≡ R236.farLowResidualExponent low high
farLowHeatResidualMatchesR236 low high = solve (low ∷ high ∷ [])

hhHeatResidualMatchesR236 :
  (output high : ℚ) →
  hhHeatResidualExponent output high
  ≡ R236.hhResidualExponent output high
hhHeatResidualMatchesR236 output high = solve (output ∷ high ∷ [])

round305HeatFactorizationPreservesCriticalResidualExponents : Bool
round305HeatFactorizationPreservesCriticalResidualExponents = true

round305HeatAlonePaysFLShoulder : Bool
round305HeatAlonePaysFLShoulder = false

round305HeatAlonePaysHHShoulder : Bool
round305HeatAlonePaysHHShoulder = false

round305HeatAlonePaysComparableRay : Bool
round305HeatAlonePaysComparableRay = false

round305AdditionalCriticalConeGainRequired : Bool
round305AdditionalCriticalConeGainRequired = true

round305PackageAClosed : Bool
round305PackageAClosed = false

round305ClayPromotion : Bool
round305ClayPromotion = false

round305AdditionalCriticalConeGainRequiredIsTrue :
  round305AdditionalCriticalConeGainRequired ≡ true
round305AdditionalCriticalConeGainRequiredIsTrue = refl
