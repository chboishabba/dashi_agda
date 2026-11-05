module DASHI.Physics.YangMills.SchutzholdR144CanonicalMetricStressCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144

------------------------------------------------------------------------
-- SCHUTZHOLD -> CANONICAL METRIC DOMAIN -> R144 STRESS COMPILER
--
-- The repo already proves, on the canonical admissible metric domain,
--
--   D_g V_eff[h] = <T , h>.
--
-- R144 already maps the global source tangent into the same substituted stress
-- activity.  This file composes those two facts.  No new stress theorem is
-- assumed: the only physical input is the same-object map from the selected
-- Schuetzhold GW perturbation into the existing canonical metric perturbation.
------------------------------------------------------------------------

record SchutzholdR144CanonicalMetricWeld
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    (r144 : R144.CompositeStressFirstVariationInputs actionWeld laws)
    {Scale Volume : Set}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume
      (R144.stressActivity r144))
    (representation : StressRep.CanonicalMetricStressRepresentation domain)
    : Set₁ where
  constructor schutzhold-r144-canonical-metric-weld
  field
    SchutzholdMetricPerturbation : Set

    toCanonicalMetricPerturbation :
      SchutzholdMetricPerturbation → Domain.MetricPerturbation domain

    schutzholdPerturbationAdmissible :
      ∀ perturbation →
      Domain.AdmissibleMetricPerturbation domain
        (toCanonicalMetricPerturbation perturbation)

    globalBackground :
      Source.Background (Carrier.source (Present.bc1Carrier present))

    globalTangent :
      SchutzholdMetricPerturbation →
      Source.Tangent (Carrier.source (Present.bc1Carrier present))

    canonicalTangentIsR144Tangent :
      ∀ perturbation →
      Domain.metricPerturbationToBackgroundTangent domain
        (R144.globalBackgroundToStressBackground r144 globalBackground)
        (toCanonicalMetricPerturbation perturbation)
      ≡
      R144.globalTangentToStressTangent r144 (globalTangent perturbation)

open SchutzholdR144CanonicalMetricWeld public

schutzholdMetricVariationIsCanonicalStressPairing :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws}
    {r144 : R144.CompositeStressFirstVariationInputs
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} actionWeld laws}
    {Scale Volume}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume
      (R144.stressActivity r144)}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (weld : SchutzholdR144CanonicalMetricWeld r144 domain representation) →
  ∀ perturbation →
  StressRep.firstVariationReadout representation
    (First.substitutedFirstVariation
      (R144.stressActivity r144)
      (R144.globalBackgroundToStressBackground r144 (globalBackground weld))
      (Domain.metricPerturbationToBackgroundTangent domain
        (R144.globalBackgroundToStressBackground r144 (globalBackground weld))
        (toCanonicalMetricPerturbation weld perturbation)))
  ≡
  StressRep.stressMetricPairing representation
    (StressRep.stressTensor representation)
    (toCanonicalMetricPerturbation weld perturbation)
schutzholdMetricVariationIsCanonicalStressPairing
    {r144 = r144} {domain = domain} {representation = representation}
    weld perturbation =
  StressRep.admittedMetricVariationEqualsStressPairing representation
    (R144.globalBackgroundToStressBackground r144 (globalBackground weld))
    (toCanonicalMetricPerturbation weld perturbation)
    (schutzholdPerturbationAdmissible weld perturbation)

schutzholdCanonicalTangentIsR144StressTangent :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws}
    {r144 : R144.CompositeStressFirstVariationInputs
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} actionWeld laws}
    {Scale Volume}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume
      (R144.stressActivity r144)}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (weld : SchutzholdR144CanonicalMetricWeld r144 domain representation) →
  ∀ perturbation →
  Domain.metricPerturbationToBackgroundTangent domain
    (R144.globalBackgroundToStressBackground r144 (globalBackground weld))
    (toCanonicalMetricPerturbation weld perturbation)
  ≡
  R144.globalTangentToStressTangent r144 (globalTangent weld perturbation)
schutzholdCanonicalTangentIsR144StressTangent weld =
  canonicalTangentIsR144Tangent weld

record SchutzholdR144CompilerBoundary : Set where
  constructor schutzhold-r144-compiler-boundary
  field
    canonicalMetricStressTheoremReused : Bool
    r144GlobalTangentMapReused : Bool
    newStressRepresentationTheoremNeeded : Bool
    remainingGWToCanonicalPerturbationIsSameObjectIdentification : Bool
    remainingAdmissibilityIsConcretePhysicalDomainCheck : Bool

canonicalSchutzholdR144CompilerBoundary : SchutzholdR144CompilerBoundary
canonicalSchutzholdR144CompilerBoundary =
  schutzhold-r144-compiler-boundary true true false true true
