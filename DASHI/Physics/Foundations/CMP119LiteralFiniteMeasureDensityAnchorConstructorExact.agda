{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureDensityAnchorConstructorExact where

open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact as FiniteSource
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanLiteralDensityNormalizedSourceRound121Exact as R121
import DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact as R122
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- FINITE-MEASURE NORMALIZED STRESS SOURCE -> R122 DENSITY ANCHOR
------------------------------------------------------------------------

record LiteralFiniteMeasureDensityAnchorInputs
    {trajectory split}
    {inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        domain representation coordinate)
    (measureWeld :
      R124.BalabanDensityLiteralFiniteMeasureWeld
        {trajectory = trajectory} {split = split} {inputs = inputs}
        Y group)
    (calculus :
      FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus measureWeld)
    : Set₁ where
  field
    selectedScale : Scale
    sourceScaleIndex : Scale → Nat

    metricPerturbationToFiniteMeasurePerturbation :
      Domain.MetricPerturbation domain →
      FiniteSource.MetricPerturbation calculus

    selectedNormalizedSourceIsFiniteMeasureSource :
      ∀ background perturbation →
      R119.normalizedSource selected background perturbation
      ≡
      R121.crossDataAt
        (FiniteSource.asLiteralDensityNormalizedStressSource calculus)
        (sourceScaleIndex selectedScale)
        (metricPerturbationToFiniteMeasurePerturbation perturbation)

open LiteralFiniteMeasureDensityAnchorInputs public

asDensityAnchoredCanonicalMetricStress :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain representation
      coordinate selected measureWeld calculus} →
  LiteralFiniteMeasureDensityAnchorInputs
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {C = C} {S = S} {Y = Y} {group = group}
    {Scale = Scale} {Volume = Volume} {activity = activity}
    {domain = domain} {representation = representation}
    {coordinate = coordinate}
    selected measureWeld calculus →
  R122.DensityAnchoredCanonicalMetricStress
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {C = C} {S = S} {Y = Y} {group = group}
    {Scale = Scale} {Volume = Volume} {activity = activity}
    {domain = domain} {representation = representation}
    {coordinate = coordinate}
    selected
asDensityAnchoredCanonicalMetricStress
    {calculus = calculus} anchorInputs = record
  { R122.DensityAnchoredCanonicalMetricStress.densitySource =
      FiniteSource.asLiteralDensityNormalizedStressSource calculus
  ; R122.DensityAnchoredCanonicalMetricStress.selectedScale =
      selectedScale anchorInputs
  ; R122.DensityAnchoredCanonicalMetricStress.sourceScaleIndex =
      sourceScaleIndex anchorInputs
  ; R122.DensityAnchoredCanonicalMetricStress.metricPerturbationToDensityPerturbation =
      metricPerturbationToFiniteMeasurePerturbation anchorInputs
  ; R122.DensityAnchoredCanonicalMetricStress.normalizedSourceIsLiteralDensity =
      selectedNormalizedSourceIsFiniteMeasureSource anchorInputs
  }
