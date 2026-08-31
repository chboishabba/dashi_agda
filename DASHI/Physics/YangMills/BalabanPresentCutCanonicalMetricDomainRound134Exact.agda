{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPresentCutCanonicalMetricDomainRound134Exact where

------------------------------------------------------------------------
-- ROUND134: ROUND122 BC1 DEMANDS/RADIUS -> ROUND106 METRIC SOURCE DOMAIN
--
-- Round131 previously accepted an independently supplied canonical metric
-- source domain.  After #644 and #638 merged, the BC1 present-cut object already
-- contains the exact finite CMP116 analytic demands and its carrier already uses
-- the canonical common radius constructed from those demands.
--
-- Therefore the stress domain should reuse that radius by construction.  Only
-- the genuinely metric-specific inputs remain: perturbation carrier/norm,
-- admissibility, tangent map and source-domain membership.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeChainRuleRound118Exact as BC1Chain
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133

record PresentCutMetricSpecificInputs
    {trajectory split inputs History Cell cutoff present actionWeld}
    (firstWeld : R133.UnifiedGeneratedActionFirstVariation
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} actionWeld) : Set₁ where
  field
    MetricPerturbation : Set
    metricPerturbationNorm : MetricPerturbation → ℚ

    AdmissibleMetricPerturbation : MetricPerturbation → Set
    admissibleMetricPerturbationBelowRadius :
      ∀ perturbation →
      AdmissibleMetricPerturbation perturbation →
      metricPerturbationNorm perturbation
      < Canon.canonicalCommonRadius
          (BC1.analyticDemands (BC1Chain.canonical (Present.bc1 present)))

    metricPerturbationToStressTangent :
      Chain.Background (R133.stressActivity firstWeld) →
      MetricPerturbation →
      Chain.BackgroundTangent (R133.stressActivity firstWeld)

    SourceTangentInside :
      Source.Scale (Carrier.source (Present.bc1Carrier present)) →
      Source.Volume (Carrier.source (Present.bc1Carrier present)) →
      Chain.Background (R133.stressActivity firstWeld) →
      Chain.BackgroundTangent (R133.stressActivity firstWeld) → Set

    admittedMetricTangentInside :
      ∀ scale volume background perturbation →
      AdmissibleMetricPerturbation perturbation →
      SourceTangentInside scale volume background
        (metricPerturbationToStressTangent background perturbation)

open PresentCutMetricSpecificInputs public

presentCutCanonicalMetricDomain :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld}
    {firstWeld : R133.UnifiedGeneratedActionFirstVariation
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} actionWeld} →
  PresentCutMetricSpecificInputs firstWeld →
  Domain.CanonicalMetricSourceDomain
    (Source.Scale (Carrier.source (Present.bc1Carrier present)))
    (Source.Volume (Carrier.source (Present.bc1Carrier present)))
    (R133.stressActivity firstWeld)
presentCutCanonicalMetricDomain {present = present} {firstWeld = firstWeld} metric = record
  { Domain.CanonicalMetricSourceDomain.demands =
      BC1.analyticDemands (BC1Chain.canonical (Present.bc1 present))
  ; Domain.CanonicalMetricSourceDomain.radiusData =
      Carrier.radiusData (Present.bc1Carrier present)
  ; Domain.CanonicalMetricSourceDomain.radiusIsCanonical = refl
  ; Domain.CanonicalMetricSourceDomain.MetricPerturbation =
      MetricPerturbation metric
  ; Domain.CanonicalMetricSourceDomain.metricPerturbationNorm =
      metricPerturbationNorm metric
  ; Domain.CanonicalMetricSourceDomain.AdmissibleMetricPerturbation =
      AdmissibleMetricPerturbation metric
  ; Domain.CanonicalMetricSourceDomain.admissibleMetricPerturbationBelowRadius =
      admissibleMetricPerturbationBelowRadius metric
  ; Domain.CanonicalMetricSourceDomain.metricPerturbationToBackgroundTangent =
      metricPerturbationToStressTangent metric
  ; Domain.CanonicalMetricSourceDomain.SourceTangentInside =
      SourceTangentInside metric
  ; Domain.CanonicalMetricSourceDomain.admittedMetricTangentInside =
      admittedMetricTangentInside metric
  }

presentCutDomainUsesExactBC1Radius :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld}
    (metric : PresentCutMetricSpecificInputs
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} {actionWeld = actionWeld} firstWeld) →
  Domain.radiusData (presentCutCanonicalMetricDomain metric)
  ≡ Carrier.radiusData (Present.bc1Carrier present)
presentCutDomainUsesExactBC1Radius metric = refl

presentCutDomainUsesExactBC1Demands :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld}
    (metric : PresentCutMetricSpecificInputs
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} {actionWeld = actionWeld} firstWeld) →
  Domain.demands (presentCutCanonicalMetricDomain metric)
  ≡ BC1.analyticDemands (BC1Chain.canonical (Present.bc1 present))
presentCutDomainUsesExactBC1Demands metric = refl

presentCutCanonicalMetricDomainCompilerLevel : ProofLevel
presentCutCanonicalMetricDomainCompilerLevel = machineChecked

-- No second analytic-radius theorem remains on the stress path.  What remains
-- conditional here is only the literal metric perturbation/tangent admission.
literalPresentCutMetricSpecificInputsLevel : ProofLevel
literalPresentCutMetricSpecificInputsLevel = conditional
