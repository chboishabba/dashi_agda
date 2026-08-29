{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact where

------------------------------------------------------------------------
-- ROUND122: CANONICAL METRIC STRESS WELD USES THE LITERAL BETA-DRIVEN DENSITY
--
-- Round119 ties the canonical CMP116 metric variation to the exact CMP119
-- insertion selected by the one-coordinate stress lane.  Round121 ensures the
-- normalized numerator/denominator source data are built on `densityAt k` of
-- the literal beta-driven complete-density trajectory.  This file welds those
-- objects pointwise, with explicit background->RG-scale and metric-perturbation
-- transports.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

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
      Domain.MetricPerturbation domain →
      R121.MetricPerturbation densitySource

    -- The normalized source used by the canonical metric weld is literally the
    -- data built from the same beta-driven density at the selected RG scale.
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
  let equality = normalizedSourceIsLiteralDensity dataSet background perturbation
  in
  Relation.Binary.PropositionalEquality.cong
    R116.sourceDerivativeCrossNumerator equality

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
    {inputs = inputs} dataSet background perturbation =
  let equality = normalizedSourceIsLiteralDensity dataSet background perturbation
  in
  Relation.Binary.PropositionalEquality.cong
    R116.connectedInsertionNumerator equality

densityAnchoredCanonicalMetricStressCompilerLevel : ProofLevel
densityAnchoredCanonicalMetricStressCompilerLevel = machineChecked

-- Physical seam remaining: exhibit the background->source scale identification
-- and perturbation transport on the actual CMP116/CMP122 construction, then
-- prove the normalized numerator/denominator data coincide definitionally/up to
-- the displayed equality.
literalCMP116CMP122DensityAnchoringLevel : ProofLevel
literalCMP116CMP122DensityAnchoringLevel = conditional
