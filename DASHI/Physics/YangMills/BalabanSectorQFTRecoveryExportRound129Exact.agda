{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact where

------------------------------------------------------------------------
-- ROUND129: PURE-YM SECTOR RECOVERY EXPORT FOR QFT/GR COMMON-METRIC CONSUMERS
--
-- PR #639 currently reconstructs a sectorwise Balaban continuum-stress theorem
-- from an abstract ConvergesTo relation.  The Round109--128 lane is stronger:
-- one literal finite-measure family, one continuum measure, one literal
-- Schwinger family, and one literal stress derivative are already tied to the
-- same source-native stress coordinate.
--
-- This module exports only native Yang--Mills facts.  It deliberately does not
-- import the TOE UnifiedCandidate/common-stress language from #639.  A later
-- thin adapter may transport this certificate into that shared representation.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanLiteralFiniteMeasureStressLaneRound125Exact as R125
import DASHI.Physics.YangMills.BalabanLiteralSchwingerStressRecoveryRound126Exact as R126
import DASHI.Physics.YangMills.BalabanSameFamilyOSStressRecoveryRound128Exact as R128
import DASHI.Physics.YangMills.BalabanCanonicalMetricStressLaneRound120Exact as R120
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record BalabanSectorQFTRecoveryExport
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
    (stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation) : Set₁ where
  field
    sameFamilyOSRecovery : R128.SameFamilyOSStressRecovery stressLane

open BalabanSectorQFTRecoveryExport public

finiteMeasureRecovery :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain representation stressLane}
    (export : BalabanSectorQFTRecoveryExport
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  R125.LiteralFiniteMeasureStressLane stressLane
finiteMeasureRecovery export =
  R126.finiteMeasureLane (R128.schwingerRecovery (sameFamilyOSRecovery export))

literalContinuumMeasureRecovery :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain representation stressLane}
    (export : BalabanSectorQFTRecoveryExport
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  Top.IsContinuumLimitOf S group
    (Top.finiteMeasure Y group)
    (Top.continuumMeasure Y group)
literalContinuumMeasureRecovery export =
  R126.literalFiniteMeasuresConverge
    (R128.schwingerRecovery (sameFamilyOSRecovery export))

literalSchwingerRecovery :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain representation stressLane}
    (export : BalabanSectorQFTRecoveryExport
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  Top.SchwingerBelongsToMeasure S
    (Top.continuumMeasure Y group)
    (Top.schwinger Y group)
literalSchwingerRecovery export =
  R126.literalSchwingerBelongsToContinuumMeasure
    (R128.schwingerRecovery (sameFamilyOSRecovery export))

literalStressDerivativeRecovery :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (export : BalabanSectorQFTRecoveryExport stressLane) →
  let selected = R120.coordinate (R123.stressLane stressLane)
      completion = R114.asMarkedCompletion selected (R114.coordinate selected)
      sources = R109.completedSources completion
      stressData = StressMarked.stressData sources
  in
  R114.cmp119CompletedResponse selected
  ≡ Marked.sourceDerivative stressData (Top.stressTensor Y group)
literalStressDerivativeRecovery {stressLane = stressLane} export =
  R123.selectedCompletionIsLiteralClayStressDerivative stressLane

metricPerturbationLanguage :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation} →
  BalabanSectorQFTRecoveryExport stressLane → Set
metricPerturbationLanguage {domain = domain} _ =
  Domain.MetricPerturbation domain

AdmissibleSectorMetricPerturbation :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation} →
  BalabanSectorQFTRecoveryExport stressLane →
  Domain.MetricPerturbation domain → Set
AdmissibleSectorMetricPerturbation {domain = domain} _ =
  Domain.AdmissibleMetricPerturbation domain

balabanSectorQFTRecoveryExportCompilerLevel : ProofLevel
balabanSectorQFTRecoveryExportCompilerLevel = machineChecked

-- This export does not create the physical evidence it exposes.  The remaining
-- source leaves are precisely those already visible in Round123--128: literal
-- metric/source identification, normalized insertion on the beta-driven density,
-- coefficient-shell instantiation, density->finite-measure identification, the
-- finite-measure continuum theorem, and source-OS -> literal-Schwinger identity.
literalBalabanSectorQFTRecoveryExportLevel : ProofLevel
literalBalabanSectorQFTRecoveryExportLevel = conditional
