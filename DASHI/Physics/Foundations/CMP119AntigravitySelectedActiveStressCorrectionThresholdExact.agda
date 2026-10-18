{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedActiveStressCorrectionThresholdExact where

------------------------------------------------------------------------
-- GRAVITY-SOURCE MAX-CUT / SAME-MEASURE QUANTITATIVE OBSTRUCTION
--
-- For the standard Lorentzian SU(2) trace+energy stress contribution:
--   A_YM = (4 κ + m) E² + m B² >= 0,  κ,m,E²,B² >= 0.
--
-- If the actual selected metric-source stress includes another contribution
-- X (from a specified nonstandard sector, boundary, background or anomalous
-- gravitational coupling), then A_selected < 0 forces X < -A_YM.
--
-- This is an exact necessary magnitude, not an assumed negative sign. The
-- SAME-MEASURE active-stress decomposition must be supplied by the selected
-- physical source; the RG running-coupling threshold does not supply it.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)

import DASHI.Physics.Foundations.CMP119AntigravityWeakCouplingTraceEnergyNoGoExact as YM

negativeTotalRequiresSupercriticalCorrection :
  ∀ baseline correction →
  baseline + correction < 0ℚ →
  correction < - baseline
negativeTotalRequiresSupercriticalCorrection baseline correction negative =
  let
    shifted :
      (baseline + correction) + (- baseline)
      < 0ℚ + (- baseline)
    shifted = ℚP.+-monoʳ-< (- baseline) negative
  in
  subst₂ _<_
    (ℚRing.solve-∀ baseline correction)
    (ℚRing.solve-∀ baseline)
    shifted

selectedNegativeStressRequiresBeyondYMCorrection :
  (dataSet : YM.WeakCouplingYMTraceEnergyData)
  (selectedActiveStress extraContribution : ℚ) →
  selectedActiveStress
    ≡ YM.activeStress dataSet + extraContribution →
  selectedActiveStress < 0ℚ →
  extraContribution < - YM.activeStress dataSet
selectedNegativeStressRequiresBeyondYMCorrection
    dataSet selectedActiveStress extraContribution sameStress negative =
  negativeTotalRequiresSupercriticalCorrection
    (YM.activeStress dataSet) extraContribution
    (subst (_< 0ℚ) sameStress negative)

-- The existing weak-coupling theorem establishes YM.activeStress >= 0.
-- Therefore a negative selected stress requires a correction that is
-- STRICTLY negative and larger in magnitude than the nonnegative YM term.
-- No such correction has been produced for the selected CMP119 measure.
