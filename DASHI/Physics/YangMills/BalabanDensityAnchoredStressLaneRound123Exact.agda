{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact where

------------------------------------------------------------------------
-- ROUND123: ONE LITERAL BETA-DRIVEN FINITE->SCHWINGER STRESS LANE
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (_≤_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricStressLaneRound120Exact as R120
import DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact as R122
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanLiteralStressCompletionRound115Exact as R115
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as ScaleCauchy
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record DensityAnchoredCanonicalMetricStressLane
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity)
    (representation : StressRep.CanonicalMetricStressRepresentation domain) : Set₁ where
  field
    stressLane : R120.CanonicalMetricLiteralStressLane
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation

    densityAnchor : R122.DensityAnchoredCanonicalMetricStress
      {trajectory = trajectory} {split = split} {inputs = inputs}
      (R120.metricSelectedStress stressLane)
open DensityAnchoredCanonicalMetricStressLane public

finiteMetricVariationUsesLiteralDensitySelectedInsertion :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (dataSet : DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation) →
  ∀ background perturbation →
  Domain.AdmissibleMetricPerturbation domain perturbation →
  let weld = R120.metricSelectedStress (stressLane dataSet)
      insertion =
        R119.R118.normalizedInsertion
          (R119.asRound118CanonicalMetricWeld weld)
          background perturbation
  in
  R119.R118.readoutToRational (R119.asRound118CanonicalMetricWeld weld)
    (StressRep.firstVariationReadout representation
      (DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact.substitutedFirstVariation
        activity background
        (Domain.metricPerturbationToBackgroundTangent domain background perturbation)))
  ≡ R116.cmp119StressInsertionNumerator insertion
finiteMetricVariationUsesLiteralDensitySelectedInsertion dataSet =
  R120.finiteMetricVariationIsSelectedCMP119Insertion (stressLane dataSet)

selectedNormalizedSourceIsLiteralBetaDrivenDensity :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (dataSet : DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation)
    background perturbation →
  R119.normalizedSource (R120.metricSelectedStress (stressLane dataSet))
      background perturbation
  ≡ DASHI.Physics.YangMills.BalabanLiteralDensityNormalizedSourceRound121Exact.crossDataAt
      (R122.densitySource (densityAnchor dataSet))
      (R122.selectedDensityScale (densityAnchor dataSet))
      (R122.metricPerturbationToDensityPerturbation
        (densityAnchor dataSet) perturbation)
selectedNormalizedSourceIsLiteralBetaDrivenDensity dataSet =
  R122.normalizedSourceIsLiteralDensity (densityAnchor dataSet)

selectedStressCauchyModulus :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (dataSet : DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation) →
  ∀ start count →
  let coordinate = R120.coordinate (stressLane dataSet)
      compiled = R115.compileLiteralStressCoordinate coordinate
      provenance = R115.provenance compiled
  in
  R109.stressDifference (R110.sourceCauchy provenance) start count
  ≤ ScaleCauchy.coefficient
      (Sum.commonMajorant
        (Source.sourceCompatibleSameFamilyIncrement
          (R109.source (R110.sourceCauchy provenance))
          (R109.smallHistory (R110.sourceCauchy provenance))
          (R109.stressInsertion (R110.sourceCauchy provenance))))
      * (Geo.half * Geo.halfPower start)
selectedStressCauchyModulus dataSet =
  R120.selectedStressCauchyModulus (stressLane dataSet)

selectedCompletionIsLiteralClayStressDerivative :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (dataSet : DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation) →
  let selected = R120.coordinate (stressLane dataSet)
      completion = R114.asMarkedCompletion selected (R114.coordinate selected)
      sources = R109.completedSources completion
      stressData = StressMarked.stressData sources
  in
  R114.cmp119CompletedResponse selected
  ≡ Marked.sourceDerivative stressData (Top.stressTensor Y group)
selectedCompletionIsLiteralClayStressDerivative dataSet =
  R120.selectedStressCompletionIsLiteralClayStressDerivative (stressLane dataSet)

densityAnchoredCanonicalMetricStressLaneCompilerLevel : ProofLevel
densityAnchoredCanonicalMetricStressLaneCompilerLevel = machineChecked

literalDensityAnchoredStressLaneInstantiationLevel : ProofLevel
literalDensityAnchoredStressLaneInstantiationLevel = conditional
