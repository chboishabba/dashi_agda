{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralSchwingerStressRecoveryRound126Exact where

------------------------------------------------------------------------
-- ROUND126: LITERAL BALABAN FINITE FAMILY -> CLAY SCHWINGER/STRESS RECOVERY
--
-- Round125 identifies the stress-generating beta-driven density with the exact
-- finite-measure family of the literal Clay construction.  This file attaches
-- only the two existing continuum semantic witnesses required to land on the
-- same continuum measure / Schwinger family.  No parallel continuum object is
-- introduced.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanLiteralFiniteMeasureStressLaneRound125Exact as R125
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record LiteralBalabanSchwingerStressRecovery
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
    finiteMeasureLane : R125.LiteralFiniteMeasureStressLane stressLane

    literalFiniteMeasuresConverge :
      Top.IsContinuumLimitOf S group
        (Top.finiteMeasure Y group)
        (Top.continuumMeasure Y group)

    literalSchwingerBelongsToContinuumMeasure :
      Top.SchwingerBelongsToMeasure S
        (Top.continuumMeasure Y group)
        (Top.schwinger Y group)
open LiteralBalabanSchwingerStressRecovery public

balabanStressGeneratingDensityIsClayFiniteMeasure :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain representation stressLane}
    (recovery : LiteralBalabanSchwingerStressRecovery
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  R125.LiteralFiniteMeasureStressLane stressLane
balabanStressGeneratingDensityIsClayFiniteMeasure = finiteMeasureLane

balabanFiniteFamilyHasLiteralClayContinuumLimit :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain representation stressLane}
    (recovery : LiteralBalabanSchwingerStressRecovery
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  Top.IsContinuumLimitOf S group
    (Top.finiteMeasure Y group)
    (Top.continuumMeasure Y group)
balabanFiniteFamilyHasLiteralClayContinuumLimit = literalFiniteMeasuresConverge

balabanContinuumMeasureHasLiteralSchwingerFamily :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain representation stressLane}
    (recovery : LiteralBalabanSchwingerStressRecovery
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane) →
  Top.SchwingerBelongsToMeasure S
    (Top.continuumMeasure Y group)
    (Top.schwinger Y group)
balabanContinuumMeasureHasLiteralSchwingerFamily =
  literalSchwingerBelongsToContinuumMeasure

literalBalabanSchwingerStressRecoveryCompilerLevel : ProofLevel
literalBalabanSchwingerStressRecoveryCompilerLevel = machineChecked

-- Physical continuum input remains the actual constructive-QFT theorem that the
-- literal finite measures converge and produce the declared Schwinger family.
-- The stress lane itself no longer uses a parallel finite or continuum object.
literalBalabanFiniteMeasureSchwingerRecoveryLevel : ProofLevel
literalBalabanFiniteMeasureSchwingerRecoveryLevel = conditional
