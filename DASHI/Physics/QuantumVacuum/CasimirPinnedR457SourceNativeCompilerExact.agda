module DASHI.Physics.QuantumVacuum.CasimirPinnedR457SourceNativeCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanLiteralFiniteMeasureStressLaneRound125Exact as R125
import DASHI.Physics.YangMills.BalabanLiteralSchwingerStressRecoveryRound126Exact as R126
import DASHI.Physics.YangMills.BalabanOSLiteralSchwingerWeldRound127Exact as R127
import DASHI.Physics.YangMills.BalabanSameFamilyOSStressRecoveryRound128Exact as R128
import DASHI.Physics.YangMills.YangMillsClayGoal1SourceNativeContinuumRound457Exact as R457
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned

------------------------------------------------------------------------
-- PINNED SOURCE-NATIVE R457 COMPILER
--
-- Once the literal Clay construction is chosen definitionally as the existing
-- pinned physical construction, its continuum-limit and Schwinger-membership
-- witnesses are already fields of that SAME pinned object.  R126 therefore
-- needs no second continuum theorem.  R128/R457 then compile from exactly:
--
--   * the R125 finite-measure stress-lane weld; and
--   * the R127 source-OS = literal-Schwinger same-object weld.
--
-- Because R457 is indexed directly by `asLiteralYangMillsConstruction pinned`,
-- no later equality `Y_R457 = Y_pinned` is physically meaningful or required.
------------------------------------------------------------------------

pinnedContinuumBuildsR126 :
  ∀ {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S)
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S}
      {Y = Pinned.asLiteralYangMillsConstruction pinned}
      {group = group}
      domain representation} →
  R125.LiteralFiniteMeasureStressLane stressLane →
  R126.LiteralBalabanSchwingerStressRecovery stressLane
pinnedContinuumBuildsR126 pinned finiteLane = record
  { R126.LiteralBalabanSchwingerStressRecovery.finiteMeasureLane = finiteLane
  ; R126.LiteralBalabanSchwingerStressRecovery.literalFiniteMeasuresConverge =
      Pinned.continuumLimit (Pinned.continuum pinned) _
  ; R126.LiteralBalabanSchwingerStressRecovery.literalSchwingerBelongsToContinuumMeasure =
      Pinned.schwingerBelongsToContinuumMeasure (Pinned.continuum pinned) _
  }

pinnedFiniteMeasureAndOSBuildR128 :
  ∀ {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S)
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S}
      {Y = Pinned.asLiteralYangMillsConstruction pinned}
      {group = group}
      domain representation} →
  R125.LiteralFiniteMeasureStressLane stressLane →
  R127.OSLiteralSchwingerWeld
    (Pinned.asLiteralYangMillsConstruction pinned) group →
  R128.SameFamilyOSStressRecovery stressLane
pinnedFiniteMeasureAndOSBuildR128 pinned finiteLane osWeld = record
  { R128.SameFamilyOSStressRecovery.schwingerRecovery =
      pinnedContinuumBuildsR126 pinned finiteLane
  ; R128.SameFamilyOSStressRecovery.osWeld = osWeld
  }

pinnedFiniteMeasureAndOSBuildR457 :
  ∀ {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S)
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S}
      {Y = Pinned.asLiteralYangMillsConstruction pinned}
      {group = group}
      domain representation} →
  R125.LiteralFiniteMeasureStressLane stressLane →
  R127.OSLiteralSchwingerWeld
    (Pinned.asLiteralYangMillsConstruction pinned) group →
  R457.SourceNativeContinuumAndOS stressLane
pinnedFiniteMeasureAndOSBuildR457 pinned finiteLane osWeld = record
  { R457.SourceNativeContinuumAndOS.sameFamilyRecovery =
      pinnedFiniteMeasureAndOSBuildR128 pinned finiteLane osWeld
  }

------------------------------------------------------------------------
-- Fail-closed accounting.
------------------------------------------------------------------------

data PinnedContinuumAutomaticallySuppliesDensityFiniteMeasureWeld : Set where
data PinnedContinuumAutomaticallySuppliesSourceOSWeld : Set where

pinnedContinuumDoesNotSupplyDensityFiniteMeasureWeld :
  PinnedContinuumAutomaticallySuppliesDensityFiniteMeasureWeld → ⊥
pinnedContinuumDoesNotSupplyDensityFiniteMeasureWeld ()

pinnedContinuumDoesNotSupplySourceOSWeld :
  PinnedContinuumAutomaticallySuppliesSourceOSWeld → ⊥
pinnedContinuumDoesNotSupplySourceOSWeld ()

record CasimirPinnedR457SourceNativeBoundary : Set where
  constructor casimir-pinned-r457-source-native-boundary
  field
    pinnedContinuumBuildsR126CompilerOwned : Bool
    pinnedFiniteMeasureAndOSBuildR457CompilerOwned : Bool
    independentR126ContinuumWitnessRequiredAfterPinned : Bool
    independentR457PinnedConstructionEqualityRequired : Bool
    literalDensityFiniteMeasureWeldStillRequired : Bool
    sourceOSLiteralSchwingerWeldStillRequired : Bool

open CasimirPinnedR457SourceNativeBoundary public

canonicalPinnedR457SourceNativeBoundary : CasimirPinnedR457SourceNativeBoundary
canonicalPinnedR457SourceNativeBoundary =
  casimir-pinned-r457-source-native-boundary true true false false true true

casimirPinnedR457SourceNativeReading : String
casimirPinnedR457SourceNativeReading =
  "On the canonical pinned route, the literal construction is definitionally asLiteralYangMillsConstruction pinned. Its continuum-limit and Schwinger-membership witnesses are already fields of the pinned continuum object, so R126 needs no second continuum theorem. R125 finite-measure identity plus the explicit source-OS/literal-Schwinger weld compile R128 and R457. The former Y_R457=Y_pinned equality is retired by construction. The genuine source payments are the beta-density -> literal finite-measure weld and the source OS -> literal Schwinger same-object weld."
