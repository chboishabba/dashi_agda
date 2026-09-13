module DASHI.Core.MeasurementAdministrationComparabilityRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.MeasurementAdministrationComparabilityExact as Measure

same-instrument-does-not-prove-comparability :
  Measure.sameInstrumentAutomaticallyComparable Measure.canonicalMeasurementComparabilityBoundary
  ≡ false
same-instrument-does-not-prove-comparability = refl

score-difference-does-not-prove-trait-difference :
  Measure.observedScoreDifferenceAutomaticallyTraitDifference Measure.canonicalMeasurementComparabilityBoundary
  ≡ false
score-difference-does-not-prove-trait-difference = refl

individual-validity-does-not-prove-pairwise-comparability :
  Measure.individualValidityAutomaticallyPairwiseComparable Measure.canonicalMeasurementComparabilityBoundary
  ≡ false
individual-validity-does-not-prove-pairwise-comparability = refl

comparability-is-consumer-indexed :
  Measure.comparabilityRequiresConsumerIndex Measure.canonicalMeasurementComparabilityBoundary
  ≡ true
comparability-is-consumer-indexed = refl

comparison-query-has-protocol-defect : Measure.ComparisonQueryAdequacyDefect
comparison-query-has-protocol-defect = Measure.comparisonQueryAdequacyDefect

comparison-query-cannot-factor-through-instrument-name :
  Measure.ComparisonQueryAdequate → ⊥
comparison-query-cannot-factor-through-instrument-name =
  Measure.comparisonQueryNotAdequate
