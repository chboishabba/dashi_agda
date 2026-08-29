{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact where

------------------------------------------------------------------------
-- ROUND105: FIRST VARIATION OF THE SAME CMP116 SUBSTITUTED ACTIVITY
--
-- Round103 correctly keeps the second-order chain-rule curvature term
--
--   D_B^2(E∘A)[u,v]
--     = D_A^2 E[A'u,A'v] + D_A E[A''(u,v)].
--
-- Stress-energy, however, is sourced by a FIRST metric/source variation.
-- At first order the same substituted activity has the ordinary chain rule
--
--   D(E∘A)[u] = D_A E[A'u],
--
-- so no second-substitution curvature term appears in this first derivative.
-- The remaining physical seam is to identify a metric perturbation with the
-- relevant background tangent and to identify the resulting first variation
-- with the literal stress tensor.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain

substitutedFirstVariation :
  (dataSet : Chain.SubstitutedActivitySecondVariation) →
  Chain.Background dataSet → Chain.BackgroundTangent dataSet → ℝ
substitutedFirstVariation dataSet background u =
  Chain.firstActivityVariation dataSet
    (Chain.substitution dataSet background)
    (Chain.firstSubstitutionVariation dataSet background u)

record PhysicalFirstVariationIdentification
    (dataSet : Chain.SubstitutedActivitySecondVariation) : Set₁ where
  field
    physicalFirstVariation :
      Chain.Background dataSet → Chain.BackgroundTangent dataSet → ℝ

    physicalFirstVariationChainRule : ∀ background u →
      physicalFirstVariation background u
      ≡ substitutedFirstVariation dataSet background u

open PhysicalFirstVariationIdentification public

record MetricPerturbationFirstVariationTransport
    (dataSet : Chain.SubstitutedActivitySecondVariation) : Set₁ where
  field
    MetricPerturbation : Set
    MetricVariationValue : Set

    metricPerturbationToBackgroundTangent :
      Chain.Background dataSet →
      MetricPerturbation → Chain.BackgroundTangent dataSet

    firstVariationReadout : ℝ → MetricVariationValue

    metricVariation :
      Chain.Background dataSet → MetricPerturbation → MetricVariationValue

    metricVariationFactorsThroughSubstitutedFirstVariation :
      ∀ background metricPerturbation →
      metricVariation background metricPerturbation
      ≡
      firstVariationReadout
        (substitutedFirstVariation dataSet background
          (metricPerturbationToBackgroundTangent
            background metricPerturbation))

open MetricPerturbationFirstVariationTransport public

record FirstVariationBoundary : Set where
  constructor firstVariationBoundary
  field
    secondBackgroundHessianNeededToDefineFirstMetricVariation : Bool
    secondBackgroundHessianNeededToDefineFirstMetricVariationIsFalse :
      secondBackgroundHessianNeededToDefineFirstMetricVariation ≡ false

    secondSubstitutionCurvatureAppearsInFirstVariation : Bool
    secondSubstitutionCurvatureAppearsInFirstVariationIsFalse :
      secondSubstitutionCurvatureAppearsInFirstVariation ≡ false

    explicitMetricToBackgroundTangentTransportStillNeeded : Bool
    explicitMetricToBackgroundTangentTransportStillNeededIsTrue :
      explicitMetricToBackgroundTangentTransportStillNeeded ≡ true

canonicalFirstVariationBoundary : FirstVariationBoundary
canonicalFirstVariationBoundary =
  firstVariationBoundary false refl false refl true refl

cmp116SubstitutedFirstVariationCompilerLevel : ProofLevel
cmp116SubstitutedFirstVariationCompilerLevel = machineChecked

metricToBackgroundFirstVariationTransportLevel : ProofLevel
metricToBackgroundFirstVariationTransportLevel = conditional
