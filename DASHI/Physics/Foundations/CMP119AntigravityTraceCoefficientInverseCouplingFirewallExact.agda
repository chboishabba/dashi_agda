{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityTraceCoefficientInverseCouplingFirewallExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.Foundations.CMP119AntigravitySU2TraceConventionExact as Trace
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta
import DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact as SU2

------------------------------------------------------------------------
-- TRACE-ANOMALY THRESHOLD COEFFICIENT != RUNNING INVERSE COUPLING VALUE
--
-- For SU(2), in the repository convention:
--
--   |b_trace| rational part = 11/48,
--   2 |b_trace|             = 11/24,
--   d(1/g^2)/d log(mu)      = 11/12,
--
-- before the common 1/pi^2 factor.
--
-- The last number is an RG SLOPE.  It is not the value 1/g^2 required by the
-- weak-coupling active-stress no-go.
------------------------------------------------------------------------

traceMagnitudeRational : ℚ
traceMagnitudeRational = + 11 / 48

twiceTraceMagnitudeRational : ℚ
twiceTraceMagnitudeRational =
  (1ℚ + 1ℚ) * traceMagnitudeRational

su2InverseCouplingSlopeRational : ℚ
su2InverseCouplingSlopeRational =
  Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir

twiceTraceMagnitudeExact :
  twiceTraceMagnitudeRational ≡ + 11 / 24
twiceTraceMagnitudeExact =
  ℚRing.solve []

inverseCouplingSlopeExact :
  su2InverseCouplingSlopeRational ≡ + 11 / 12
inverseCouplingSlopeExact =
  Trace.su2InverseCouplingCoefficientExact

slopeIsTwiceNoGoThreshold :
  su2InverseCouplingSlopeRational
  ≡
  (1ℚ + 1ℚ) * twiceTraceMagnitudeRational
slopeIsTwiceNoGoThreshold =
  ℚRing.solve []

rgSlopeCanBeSubstitutedForInverseCouplingValue : Bool
rgSlopeCanBeSubstitutedForInverseCouplingValue = false

rgSlopeCanBeSubstitutedForInverseCouplingValueIsFalse :
  rgSlopeCanBeSubstitutedForInverseCouplingValue ≡ false
rgSlopeCanBeSubstitutedForInverseCouplingValueIsFalse = refl

selectedInverseCouplingValueLowerBoundStillRequired : Bool
selectedInverseCouplingValueLowerBoundStillRequired = true

selectedInverseCouplingValueLowerBoundStillRequiredIsTrue :
  selectedInverseCouplingValueLowerBoundStillRequired ≡ true
selectedInverseCouplingValueLowerBoundStillRequiredIsTrue = refl

selectedWeakCouplingNoGoThresholdRational : ℚ
selectedWeakCouplingNoGoThresholdRational = + 11 / 24
