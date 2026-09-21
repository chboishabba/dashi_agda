{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanR144CanonicalMetricDomainRound433Exact where

------------------------------------------------------------------------
-- C / ROUND433: CONSTRUCT THE CANONICAL METRIC DOMAIN FROM THE R144 TANGENT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _<_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain

record R144CanonicalMetricDomainData
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    (composite : R144.CompositeStressFirstVariationInputs actionWeld laws)
    (Scale Volume : Set) : Set₁ where
  field
    demands : Canon.CMP116FiniteNormalizedAnalyticDemands
    radiusData : Radius.CMP116CommonAnalyticRadius Scale Volume
    radiusIsCanonical :
      Radius.radius radiusData ≡ Canon.canonicalCommonRadius demands

    metricPerturbationNorm :
      Source.Tangent (Carrier.source (Present.bc1Carrier present)) → ℚ

    AdmissibleMetricPerturbation :
      Source.Tangent (Carrier.source (Present.bc1Carrier present)) → Set

    admissibleMetricPerturbationBelowRadius :
      ∀ tangent →
      AdmissibleMetricPerturbation tangent →
      metricPerturbationNorm tangent < Canon.canonicalCommonRadius demands

    StressTangentInside :
      Scale → Volume →
      Chain.Background (R144.stressActivity composite) →
      Chain.BackgroundTangent (R144.stressActivity composite) → Set

    admittedR144StressTangentInside :
      ∀ scale volume stressBackground tangent →
      AdmissibleMetricPerturbation tangent →
      StressTangentInside scale volume stressBackground
        (R144.globalTangentToStressTangent composite tangent)

open R144CanonicalMetricDomainData public

asCanonicalMetricSourceDomain :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws}
    (composite :
      R144.CompositeStressFirstVariationInputs
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} actionWeld laws)
    {Scale Volume} →
  R144CanonicalMetricDomainData composite Scale Volume →
  Domain.CanonicalMetricSourceDomain
    Scale Volume (R144.stressActivity composite)
asCanonicalMetricSourceDomain composite data = record
  { Domain.CanonicalMetricSourceDomain.demands = demands data
  ; Domain.CanonicalMetricSourceDomain.radiusData = radiusData data
  ; Domain.CanonicalMetricSourceDomain.radiusIsCanonical =
      radiusIsCanonical data
  ; Domain.CanonicalMetricSourceDomain.MetricPerturbation =
      Source.Tangent (Carrier.source _)
  ; Domain.CanonicalMetricSourceDomain.metricPerturbationNorm =
      metricPerturbationNorm data
  ; Domain.CanonicalMetricSourceDomain.AdmissibleMetricPerturbation =
      AdmissibleMetricPerturbation data
  ; Domain.CanonicalMetricSourceDomain.admissibleMetricPerturbationBelowRadius =
      admissibleMetricPerturbationBelowRadius data
  ; Domain.CanonicalMetricSourceDomain.metricPerturbationToBackgroundTangent =
      λ _ tangent → R144.globalTangentToStressTangent composite tangent
  ; Domain.CanonicalMetricSourceDomain.SourceTangentInside =
      StressTangentInside data
  ; Domain.CanonicalMetricSourceDomain.admittedMetricTangentInside =
      admittedR144StressTangentInside data
  }

r144MetricPerturbationRealizesStressTangent :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws
      composite Scale Volume}
    (data :
      R144CanonicalMetricDomainData
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} {actionWeld = actionWeld} {laws = laws}
        composite Scale Volume)
    stressBackground tangent →
  Domain.metricPerturbationToBackgroundTangent
    (asCanonicalMetricSourceDomain composite data)
    stressBackground tangent
  ≡ R144.globalTangentToStressTangent composite tangent
r144MetricPerturbationRealizesStressTangent data stressBackground tangent = refl

round433R144MetricTangentDefinitionLevel : ProofLevel
round433R144MetricTangentDefinitionLevel = machineChecked

-- Remaining source content is only the common-radius/admissibility membership
-- for the literal metric perturbation; the tangent same-object equality is gone.
literalRound433MetricAdmissibilityLevel : ProofLevel
literalRound433MetricAdmissibilityLevel = conditional
