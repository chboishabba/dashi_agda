{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySU2TraceConventionExact where

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; Positive; positive; _*_; -_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta
import DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact as SU2

------------------------------------------------------------------------
-- PURE SU(2) TRACE-ANOMALY COEFFICIENT IN THE REPOSITORY'S CONVENTION
--
-- Repo convention:
--
--   d(1/g^2) / d log(mu)
--     = pureYMInverseCouplingCoefficient(C_A) / pi^2
--
-- and for SU(2), C_A=2:
--
--   pureYMInverseCouplingCoefficient = 11/12.
--
-- For a gauge action normalized as
--
--   L = (1/(4 g^2)) F^2,
--
-- the pure-gauge trace coefficient multiplying the SAME F^2 convention is
--
--   b_trace = -(1/4) d(1/g^2)/d log(mu).
--
-- Hence the rational coefficient multiplying 1/pi^2 is exactly -11/48.
--
-- The positive 1/pi^2 factor is NOT silently converted to a rational.  A
-- same-object attachment must either keep that factor in the coefficient
-- carrier or absorb it explicitly into the normalized F^2 numerator.
------------------------------------------------------------------------

quarter : ℚ
quarter = + 1 / 4

su2InverseCouplingRationalCoefficient : ℚ
su2InverseCouplingRationalCoefficient =
  Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir

su2TraceRationalCoefficient : ℚ
su2TraceRationalCoefficient =
  - (quarter * su2InverseCouplingRationalCoefficient)

su2InverseCouplingCoefficientExact :
  su2InverseCouplingRationalCoefficient ≡ + 11 / 12
su2InverseCouplingCoefficientExact =
  SU2.su2InverseCouplingCoefficientExact

su2TraceCoefficientExact :
  su2TraceRationalCoefficient ≡ - (+ 11 / 48)
su2TraceCoefficientExact = ℚRing.solve []

elevenOverFortyEightPositive :
  0ℚ < (+ 11 / 48)
elevenOverFortyEightPositive = ℚP.positive⁻¹ (+ 11 / 48)

su2TraceCoefficientNegative :
  su2TraceRationalCoefficient < 0ℚ
su2TraceCoefficientNegative =
  let
    reflected :
      - (+ 11 / 48) < - 0ℚ
    reflected =
      ℚP.neg-mono-< elevenOverFortyEightPositive
  in
  subst
    (λ left → left < 0ℚ)
    (sym su2TraceCoefficientExact)
    (subst
      (λ right → - (+ 11 / 48) < right)
      (ℚRing.solve [])
      reflected)

record SU2TraceConventionBoundary : Set₁ where
  field
    normalizedF2Numerator : ℚ

    -- This equality is the convention-sensitive same-object weld:
    -- the selected renormalized trace numerator must use the SAME action/F^2
    -- normalization as the inverse-coupling coefficient above, including the
    -- positive 1/pi^2 normalization factor.
    selectedQuantumTraceNumerator : ℚ

    selectedTraceUsesSU2Convention :
      selectedQuantumTraceNumerator
      ≡ su2TraceRationalCoefficient * normalizedF2Numerator

open SU2TraceConventionBoundary public
