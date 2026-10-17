module DASHI.Physics.QuantumVacuum.CasimirPinnedR457SourceNativeCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanCanonicalMetricStressLaneRound120Exact as R120
import DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact as R122
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
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
-- Packaging chain:
--   R114 + R119 -> R120
--   R120 + R122 -> R123
--   R123 + R124 -> R125
--   pinned continuum + R125 -> R126
--   R126 + R127 -> R128 -> R457.
--
-- Therefore R120/R123/R125/R126 and Y_R457=Y_pinned are not primitive physics
-- payments on the canonical pinned route.
------------------------------------------------------------------------

r114AndR119BuildR120 :
  ∀ {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S)
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate
      (Pinned.asLiteralYangMillsConstruction pinned) group} →
  R119.CanonicalMetricSelectedStressWeld
    domain representation coordinate →
  R120.CanonicalMetricLiteralStressLane
    {C = C} {S = S}
    {Y = Pinned.asLiteralYangMillsConstruction pinned}
    {group = group}
    domain representation
r114AndR119BuildR120 pinned {coordinate = coordinate} selected = record
  { R120.CanonicalMetricLiteralStressLane.coordinate = coordinate
  ; R120.CanonicalMetricLiteralStressLane.metricSelectedStress = selected
  }

r120AndR122BuildR123 :
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
    (metricLane : R120.CanonicalMetricLiteralStressLane
      {C = C} {S = S}
      {Y = Pinned.asLiteralYangMillsConstruction pinned}
      {group = group}
      domain representation) →
  R122.DensityAnchoredCanonicalMetricStress
    (R120.metricSelectedStress metricLane) →
  R123.DensityAnchoredCanonicalMetricStressLane
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {C = C} {S = S}
    {Y = Pinned.asLiteralYangMillsConstruction pinned}
    {group = group}
    domain representation
r120AndR122BuildR123 pinned metricLane densityAnchor = record
  { R123.DensityAnchoredCanonicalMetricStressLane.stressLane = metricLane
  ; R123.DensityAnchoredCanonicalMetricStressLane.densityAnchor = densityAnchor
  }

r123AndR124BuildR125 :
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
    (stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S}
      {Y = Pinned.asLiteralYangMillsConstruction pinned}
      {group = group}
      domain representation) →
  R124.BalabanDensityLiteralFiniteMeasureWeld
    {trajectory = trajectory} {split = split} {inputs = inputs}
    (Pinned.asLiteralYangMillsConstruction pinned) group →
  R125.LiteralFiniteMeasureStressLane stressLane
r123AndR124BuildR125 pinned stressLane measureWeld = record
  { R125.LiteralFiniteMeasureStressLane.measureWeld = measureWeld }

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
pinnedContinuumBuildsR126 pinned {group = group} finiteLane = record
  { R126.LiteralBalabanSchwingerStressRecovery.finiteMeasureLane = finiteLane
  ; R126.LiteralBalabanSchwingerStressRecovery.literalFiniteMeasuresConverge =
      Pinned.continuumLimit (Pinned.continuum pinned) group
  ; R126.LiteralBalabanSchwingerStressRecovery.literalSchwingerBelongsToContinuumMeasure =
      Pinned.schwingerBelongsToContinuumMeasure (Pinned.continuum pinned) group
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

pinnedPrimitiveSourceInputsBuildR457 :
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
    {coordinate : R114.LiteralStressCoordinate
      (Pinned.asLiteralYangMillsConstruction pinned) group}
    (selected : R119.CanonicalMetricSelectedStressWeld
      domain representation coordinate) →
  (densityAnchor : R122.DensityAnchoredCanonicalMetricStress selected) →
  R124.BalabanDensityLiteralFiniteMeasureWeld
    {trajectory = trajectory} {split = split} {inputs = inputs}
    (Pinned.asLiteralYangMillsConstruction pinned) group →
  R127.OSLiteralSchwingerWeld
    (Pinned.asLiteralYangMillsConstruction pinned) group →
  let metricLane = r114AndR119BuildR120 pinned selected
      stressLane = r120AndR122BuildR123 pinned metricLane densityAnchor
  in R457.SourceNativeContinuumAndOS stressLane
pinnedPrimitiveSourceInputsBuildR457
    pinned selected densityAnchor measureWeld osWeld =
  let metricLane = r114AndR119BuildR120 pinned selected
      stressLane = r120AndR122BuildR123 pinned metricLane densityAnchor
      finiteLane = r123AndR124BuildR125 pinned stressLane measureWeld
  in pinnedFiniteMeasureAndOSBuildR457 pinned finiteLane osWeld

------------------------------------------------------------------------
-- Fail-closed accounting.
------------------------------------------------------------------------

data PinnedContinuumAutomaticallySuppliesDensityFiniteMeasureWeld : Set where
data PinnedContinuumAutomaticallySuppliesSourceOSWeld : Set where
data SelectedStressAutomaticallySuppliesDensityAnchor : Set where

pinnedContinuumDoesNotSupplyDensityFiniteMeasureWeld :
  PinnedContinuumAutomaticallySuppliesDensityFiniteMeasureWeld → ⊥
pinnedContinuumDoesNotSupplyDensityFiniteMeasureWeld ()

pinnedContinuumDoesNotSupplySourceOSWeld :
  PinnedContinuumAutomaticallySuppliesSourceOSWeld → ⊥
pinnedContinuumDoesNotSupplySourceOSWeld ()

selectedStressDoesNotSupplyDensityAnchor :
  SelectedStressAutomaticallySuppliesDensityAnchor → ⊥
selectedStressDoesNotSupplyDensityAnchor ()

record CasimirPinnedR457SourceNativeBoundary : Set where
  constructor casimir-pinned-r457-source-native-boundary
  field
    r114AndR119BuildR120CompilerOwned : Bool
    r120AndR122BuildR123CompilerOwned : Bool
    r123AndR124BuildR125CompilerOwned : Bool
    pinnedContinuumBuildsR126CompilerOwned : Bool
    pinnedPrimitiveSourceInputsBuildR457CompilerOwned : Bool
    independentR120StressLaneRequiredAfterR114R119 : Bool
    independentR123StressLaneRequiredAfterR120R122 : Bool
    independentR125FiniteMeasureLaneRequiredAfterR124 : Bool
    independentR126ContinuumWitnessRequiredAfterPinned : Bool
    independentR457PinnedConstructionEqualityRequired : Bool
    literalStressCoordinateStillRequired : Bool
    canonicalMetricSelectedStressSemanticsStillRequired : Bool
    literalDensityAnchoringStillRequired : Bool
    literalDensityFiniteMeasureWeldStillRequired : Bool
    sourceOSLiteralSchwingerWeldStillRequired : Bool

open CasimirPinnedR457SourceNativeBoundary public

canonicalPinnedR457SourceNativeBoundary : CasimirPinnedR457SourceNativeBoundary
canonicalPinnedR457SourceNativeBoundary =
  casimir-pinned-r457-source-native-boundary
    true true true true true false false false false false true true true true true

casimirPinnedR457SourceNativeReading : String
casimirPinnedR457SourceNativeReading =
  "The canonical pinned R457 path is contracted to the first semantic/source payments. R120 is only R114 literal stress coordinate plus R119 selected metric-stress semantics; R123 is R120 plus R122 literal-density anchoring; R125 is R123 plus R124 density-to-literal-finite-measure identity. The pinned continuum object supplies R126 continuum and Schwinger witnesses definitionally. R127 then closes R128/R457. No independent R120/R123/R125/R126 or Y_R457=Y_pinned theorem remains. The local source leaves are therefore R114, R119, R122, R124 and R127; construction of the pinned Yang-Mills object itself remains an upstream Yang-Mills theorem dependency rather than a Casimir-local payment."
