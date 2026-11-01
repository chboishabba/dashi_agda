{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCommonMetricSectorRecoveryRound131Exact where

------------------------------------------------------------------------
-- ROUND131: COMMON-METRIC-READY PURE-YM SECTOR RECOVERY
--
-- This is the forward BIDI producer intended for the QFT side of PR #639.
-- It packages the same-family finite/continuum/Schwinger provenance from
-- Round129 with the nuclear-test -> metric-pairing representation weld from
-- Round130.  No UnifiedCandidate or total-QFT aggregation appears here.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.BalabanContinuumMetricStressPairingRound130Exact as R130
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record CommonMetricReadyBalabanSectorRecovery
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
    qftRecovery : R129.BalabanSectorQFTRecoveryExport stressLane
    metricPairing : R130.ContinuumMetricStressPairingWeld stressLane

open CommonMetricReadyBalabanSectorRecovery public

continuumSectorFirstVariation :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation} →
  CommonMetricReadyBalabanSectorRecovery stressLane →
  Domain.MetricPerturbation domain → StressRep.PairingScalar representation
continuumSectorFirstVariation recovery perturbation =
  let weld = metricPairing recovery
      selected = R130.selectedCoordinate weld
  in
  R130.continuumValueToPairingScalar weld
    (R114.cmp119CompletedResponse selected
      (R130.metricPerturbationToNuclearTest weld perturbation))

continuumSectorFirstVariationIsLiteralStressPairing :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (recovery : CommonMetricReadyBalabanSectorRecovery stressLane) →
  ∀ perturbation →
  Domain.AdmissibleMetricPerturbation domain perturbation →
  continuumSectorFirstVariation recovery perturbation
  ≡ StressRep.stressMetricPairing representation
      (StressRep.stressTensor representation) perturbation
continuumSectorFirstVariationIsLiteralStressPairing recovery =
  R130.completedStressFunctionalEqualsCanonicalStressPairing
    (metricPairing recovery)

literalFiniteFamilyContinuumRecovery :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (recovery : CommonMetricReadyBalabanSectorRecovery stressLane) →
  Top.IsContinuumLimitOf S group
    (Top.finiteMeasure Y group)
    (Top.continuumMeasure Y group)
literalFiniteFamilyContinuumRecovery recovery =
  R129.literalContinuumMeasureRecovery (qftRecovery recovery)

literalSchwingerFamilyRecovery :
  ∀ {trajectory split inputs C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (recovery : CommonMetricReadyBalabanSectorRecovery stressLane) →
  Top.SchwingerBelongsToMeasure S
    (Top.continuumMeasure Y group)
    (Top.schwinger Y group)
literalSchwingerFamilyRecovery recovery =
  R129.literalSchwingerRecovery (qftRecovery recovery)

commonMetricReadyBalabanSectorCompilerLevel : ProofLevel
commonMetricReadyBalabanSectorCompilerLevel = machineChecked

-- After this object is instantiated, a TOE/common-action consumer should need
-- only representation transport into its shared stress carrier, common metric
-- perturbation transport, and exact sector aggregation.  It should not ask for
-- a second independent stress-convergence relation.
literalCommonMetricReadyBalabanSectorLevel : ProofLevel
literalCommonMetricReadyBalabanSectorLevel = conditional
