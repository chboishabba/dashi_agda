{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Exact where

------------------------------------------------------------------------
-- GOAL-1 B1 / ROUND575:
-- PREFERRED R278 RATIONAL COVARIANCE EXTENSION HAS MAGNITUDE = ABS BY CONSTRUCTION
--
-- R278 keeps negate/magnitude abstract because it is scalar-generic.  On the
-- preferred rational Wilson lane, choosing a second arbitrary magnitude map and
-- later proving
--
--     magnitude x = |x|
--
-- is representation debt.
--
-- R575 chooses the rational operations at construction time:
--
--     negate    := rational negation
--     magnitude := rational absolute value.
--
-- What remains imported/standard is only continuity of multiplication,
-- negation and absolute value for the chosen scalar convergence relation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; -_; ∣_∣)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278

record RationalCovarianceContinuityLaws
    {Measure Observable : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    : Set₁ where
  field
    multiplyConverges :
      (firstSequence secondSequence : Nat → ℚ)
      (firstLimit secondLimit : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet)
        firstSequence firstLimit →
      Gram.Converges (Gram.scalarConvergence dataSet)
        secondSequence secondLimit →
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff →
          Gram.multiply (Gram.operations dataSet)
            (firstSequence cutoff) (secondSequence cutoff))
        (Gram.multiply (Gram.operations dataSet)
          firstLimit secondLimit)

    negateConverges :
      (sequence : Nat → ℚ) (limit : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence limit →
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff → - sequence cutoff)
        (- limit)

    absoluteConverges :
      (sequence : Nat → ℚ) (limit : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence limit →
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff → ∣ sequence cutoff ∣)
        ∣ limit ∣

open RationalCovarianceContinuityLaws public

rationalAbsoluteCovarianceExtension :
  ∀ {Measure Observable}
    {dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ} →
  RationalCovarianceContinuityLaws dataSet →
  R278.ScalarCovarianceConvergenceExtension dataSet
rationalAbsoluteCovarianceExtension laws = record
  { R278.ScalarCovarianceConvergenceExtension.negate =
      -_
  ; R278.ScalarCovarianceConvergenceExtension.magnitude =
      ∣_∣
  ; R278.ScalarCovarianceConvergenceExtension.multiplyConverges =
      multiplyConverges laws
  ; R278.ScalarCovarianceConvergenceExtension.negateConverges =
      negateConverges laws
  ; R278.ScalarCovarianceConvergenceExtension.magnitudeConverges =
      absoluteConverges laws
  }

magnitudeIsRationalAbsolute :
  ∀ {Measure Observable}
    {dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    (laws : RationalCovarianceContinuityLaws dataSet)
    value →
  R278.magnitude
    (rationalAbsoluteCovarianceExtension laws)
    value
  ≡
  ∣ value ∣
magnitudeIsRationalAbsolute laws value = refl

negateIsRationalNegation :
  ∀ {Measure Observable}
    {dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    (laws : RationalCovarianceContinuityLaws dataSet)
    value →
  R278.negate
    (rationalAbsoluteCovarianceExtension laws)
    value
  ≡
  - value
negateIsRationalNegation laws value = refl

round575RationalCovarianceExtensionCompilerLevel : ProofLevel
round575RationalCovarianceExtensionCompilerLevel = machineChecked

round575MagnitudeCalibrationCompilerLevel : ProofLevel
round575MagnitudeCalibrationCompilerLevel = machineChecked

round575NegationCalibrationCompilerLevel : ProofLevel
round575NegationCalibrationCompilerLevel = machineChecked

-- These are ordinary scalar-convergence facts, not Wilson/YM source theorems.
round575RationalCovarianceContinuityLawsLevel : ProofLevel
round575RationalCovarianceContinuityLawsLevel = standardImported
