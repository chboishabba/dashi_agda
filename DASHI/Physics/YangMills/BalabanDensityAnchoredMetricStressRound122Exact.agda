{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact where

open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanLiteralDensityNormalizedSourceRound121Exact as R121
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record DensityAnchoredCanonicalMetricStress
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
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
    (metricWeld : R119.CanonicalMetricSelectedStressWeld
      domain representation coordinate) : Set₁ where
  field
    densitySource : R121.LiteralDensityNormalizedStressSource inputs
    backgroundScale : Chain.Background activity → Nat
    metricPerturbationToDensityPerturbation :
      Domain.MetricPerturbation domain → R121.MetricPerturbation densitySource
    normalizedSourceIsLiteralDensity :
      ∀ background perturbation →
      R119.normalizedSource metricWeld background perturbation
      ≡ R121.crossDataAt densitySource
          (backgroundScale background)
          (metricPerturbationToDensityPerturbation perturbation)
open DensityAnchoredCanonicalMetricStress public

canonicalMetricCrossNumeratorIsLiteralDensityCrossNumerator :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain representation coordinate metricWeld}
    (dataSet : DensityAnchoredCanonicalMetricStress
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation} {coordinate = coordinate}
      metricWeld)
    background perturbation →
  R116.sourceDerivativeCrossNumerator
    (R119.normalizedSource metricWeld background perturbation)
  ≡ R116.sourceDerivativeCrossNumerator
      (R121.crossDataAt (densitySource dataSet)
        (backgroundScale dataSet background)
        (metricPerturbationToDensityPerturbation dataSet perturbation))
canonicalMetricCrossNumeratorIsLiteralDensityCrossNumerator
    dataSet background perturbation =
  cong R116.sourceDerivativeCrossNumerator
    (normalizedSourceIsLiteralDensity dataSet background perturbation)

canonicalMetricConnectedInsertionIsOnLiteralDensity :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain representation coordinate metricWeld}
    (dataSet : DensityAnchoredCanonicalMetricStress
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation} {coordinate = coordinate}
      metricWeld)
    background perturbation →
  R116.connectedInsertionNumerator
    (R119.normalizedSource metricWeld background perturbation)
  ≡ R121.connectedInsertionNumerator (densitySource dataSet)
      (BetaDensity.densityAt inputs (backgroundScale dataSet background))
      (metricPerturbationToDensityPerturbation dataSet perturbation)
canonicalMetricConnectedInsertionIsOnLiteralDensity
    dataSet background perturbation =
  cong R116.connectedInsertionNumerator
    (normalizedSourceIsLiteralDensity dataSet background perturbation)

densityAnchoredCanonicalMetricStressCompilerLevel : ProofLevel
densityAnchoredCanonicalMetricStressCompilerLevel = machineChecked

literalCMP116CMP122DensityAnchoringLevel : ProofLevel
literalCMP116CMP122DensityAnchoringLevel = conditional
