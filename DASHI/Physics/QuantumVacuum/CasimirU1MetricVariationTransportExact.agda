module DASHI.Physics.QuantumVacuum.CasimirU1MetricVariationTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact as PathDerivative

------------------------------------------------------------------------
-- SAME-METRIC-PATH ACTION EQUALITY -> FIRST-VARIATION EQUALITY
--
-- The CMP119 P1 lane already owns the only analytic transport needed here:
-- derivativeAtZero respects pointwise equality of one-variable functions.
-- Therefore, if restricted YM and Maxwell are the SAME action family along one
-- declared metric path, equality of their metric first variations is compiler
-- output.  A second independent "restriction commutes with metric variation"
-- theorem is not required.
--
-- This does NOT identify the metric path, prove action equality along every
-- point of that path, or normalize the stress readout.  Those remain physical
-- same-object payments.
------------------------------------------------------------------------

record SameMetricPathActionFamily : Set₁ where
  field
    MetricConfiguration : Set
    MetricPerturbation : Set

    metricPath :
      MetricConfiguration → MetricPerturbation → ℝ → MetricConfiguration

    restrictedYMActionAt : MetricConfiguration → ℝ
    maxwellActionAt : MetricConfiguration → ℝ

    sameActionAlongMetricPath :
      ∀ background perturbation t →
      restrictedYMActionAt (metricPath background perturbation t)
      ≡ maxwellActionAt (metricPath background perturbation t)

    reading : String

open SameMetricPathActionFamily public

restrictedYMMetricFirstVariation :
  PathDerivative.SignedPathDerivativeLaws →
  SameMetricPathActionFamily →
  MetricConfiguration _ → MetricPerturbation _ → ℝ
restrictedYMMetricFirstVariation derivative family background perturbation =
  PathDerivative.derivativeAtZero derivative
    (λ t → restrictedYMActionAt family
      (metricPath family background perturbation t))

maxwellMetricFirstVariation :
  PathDerivative.SignedPathDerivativeLaws →
  SameMetricPathActionFamily →
  MetricConfiguration _ → MetricPerturbation _ → ℝ
maxwellMetricFirstVariation derivative family background perturbation =
  PathDerivative.derivativeAtZero derivative
    (λ t → maxwellActionAt family
      (metricPath family background perturbation t))

sameMetricPathActionEqualityImpliesVariationEquality :
  (derivative : PathDerivative.SignedPathDerivativeLaws) →
  (family : SameMetricPathActionFamily) →
  ∀ background perturbation →
  restrictedYMMetricFirstVariation derivative family background perturbation
  ≡ maxwellMetricFirstVariation derivative family background perturbation
sameMetricPathActionEqualityImpliesVariationEquality
    derivative family background perturbation =
  PathDerivative.derivativeCong derivative
    (λ t → restrictedYMActionAt family
      (metricPath family background perturbation t))
    (λ t → maxwellActionAt family
      (metricPath family background perturbation t))
    (sameActionAlongMetricPath family background perturbation)

------------------------------------------------------------------------
-- Shared stress readout compiler.
--
-- If the SAME stress-construction/readout consumes the scalar first variation,
-- equality of first variations transports by ordinary congruence.  This is not
-- a normalization theorem: the actual physical readout must still be supplied.
------------------------------------------------------------------------

record CommonStressReadout : Set₁ where
  field
    StressCarrier : Set
    stressFromFirstVariation : ℝ → StressCarrier
    reading : String

open CommonStressReadout public

sameVariationImpliesSameCommonStressReadout :
  ∀ {leftVariation rightVariation : ℝ} →
  (readout : CommonStressReadout) →
  leftVariation ≡ rightVariation →
  stressFromFirstVariation readout leftVariation
  ≡ stressFromFirstVariation readout rightVariation
sameVariationImpliesSameCommonStressReadout readout =
  cong (stressFromFirstVariation readout)

------------------------------------------------------------------------
-- Firewalls / status.
------------------------------------------------------------------------

data EqualActionAtOneMetricAutomaticallyEqualsVariations : Set where
data SamePathVariationEqualityAutomaticallyFixesStressNormalization : Set where

equalActionAtOneMetricDoesNotEqualVariations :
  EqualActionAtOneMetricAutomaticallyEqualsVariations → ⊥
equalActionAtOneMetricDoesNotEqualVariations ()

variationEqualityDoesNotFixStressNormalization :
  SamePathVariationEqualityAutomaticallyFixesStressNormalization → ⊥
variationEqualityDoesNotFixStressNormalization ()

record CasimirU1MetricVariationTransportBoundary : Set where
  constructor casimir-u1-metric-variation-transport-boundary
  field
    cmp119DerivativeCongruenceReused : Bool
    sameMetricPathActionEqualityToVariationEqualityCompilerOwned : Bool
    independentMetricVariationEqualityRequiredAfterSamePathActionEquality : Bool
    sameMetricPathActionFamilyStillRequired : Bool
    metricVariationToStressReadoutStillRequired : Bool

open CasimirU1MetricVariationTransportBoundary public

canonicalU1MetricVariationTransportBoundary : CasimirU1MetricVariationTransportBoundary
canonicalU1MetricVariationTransportBoundary =
  casimir-u1-metric-variation-transport-boundary true true false true true

casimirU1MetricVariationTransportReading : String
casimirU1MetricVariationTransportReading =
  "CMP119 P1 derivative congruence compiles pointwise equality of restricted-YM and Maxwell actions along the SAME metric path into equality of their first metric variations. Therefore metric-variation commutation is not an independent theorem after a common path/action-family payment. A common stress readout then transports variation equality by congruence, but the actual metric path, action equality along the full path, and physical stress normalization/readout remain independent same-object payments. Equality at only one metric is explicitly insufficient."
