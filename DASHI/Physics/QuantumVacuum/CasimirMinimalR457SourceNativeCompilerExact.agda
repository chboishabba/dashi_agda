module DASHI.Physics.QuantumVacuum.CasimirMinimalR457SourceNativeCompilerExact where

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

------------------------------------------------------------------------
-- MINIMAL CASIMIR/R457 SOURCE-NATIVE COMPILER
--
-- Casimir stress recovery does not consume the full PinnedYangMillsConstruction
-- package.  In particular, no physical mass-gap/SI package is needed merely to
-- transport one literal construction through the R114..R128 stress lane.
--
-- The actual construction-level inputs used by R126 are only:
--   * one literal Yang-Mills construction Y;
--   * finiteMeasure(Y) -> continuumMeasure(Y);
--   * schwinger(Y) belongs to continuumMeasure(Y).
--
-- Everything else below is the already-existing R114/R119/R122/R124/R127
-- source semantics.  This prevents the Casimir lane from spuriously requiring
-- a proof of the Clay mass gap before an electromagnetic stress attachment can
-- even be stated.
------------------------------------------------------------------------

record MinimalContinuumSchwingerAttachment
    {C : Top.LiteralYangMillsCarriers}
    (S : Top.LiteralYangMillsSemantics C)
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C) : Set₁ where
  field
    literalFiniteMeasuresConverge :
      Top.IsContinuumLimitOf S group
        (Top.finiteMeasure Y group)
        (Top.continuumMeasure Y group)

    literalSchwingerBelongsToContinuumMeasure :
      Top.SchwingerBelongsToMeasure S
        (Top.continuumMeasure Y group)
        (Top.schwinger Y group)

open MinimalContinuumSchwingerAttachment public

r114AndR119BuildR120 :
  ∀ {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group} →
  R119.CanonicalMetricSelectedStressWeld
    domain representation coordinate →
  R120.CanonicalMetricLiteralStressLane
    {C = C} {S = S} {Y = Y} {group = group}
    domain representation
r114AndR119BuildR120 {coordinate = coordinate} selected = record
  { R120.CanonicalMetricLiteralStressLane.coordinate = coordinate
  ; R120.CanonicalMetricLiteralStressLane.metricSelectedStress = selected
  }

r120AndR122BuildR123 :
  ∀ {trajectory split}
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
    (metricLane : R120.CanonicalMetricLiteralStressLane
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation) →
  R122.DensityAnchoredCanonicalMetricStress
    (R120.metricSelectedStress metricLane) →
  R123.DensityAnchoredCanonicalMetricStressLane
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {C = C} {S = S} {Y = Y} {group = group}
    domain representation
r120AndR122BuildR123 metricLane densityAnchor = record
  { R123.DensityAnchoredCanonicalMetricStressLane.stressLane = metricLane
  ; R123.DensityAnchoredCanonicalMetricStressLane.densityAnchor = densityAnchor
  }

r123AndR124BuildR125 :
  ∀ {trajectory split}
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
      domain representation) →
  R124.BalabanDensityLiteralFiniteMeasureWeld
    {trajectory = trajectory} {split = split} {inputs = inputs}
    Y group →
  R125.LiteralFiniteMeasureStressLane stressLane
r123AndR124BuildR125 stressLane measureWeld = record
  { R125.LiteralFiniteMeasureStressLane.measureWeld = measureWeld }

minimalContinuumBuildsR126 :
  ∀ {trajectory split}
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
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation} →
  MinimalContinuumSchwingerAttachment S Y group →
  R125.LiteralFiniteMeasureStressLane stressLane →
  R126.LiteralBalabanSchwingerStressRecovery stressLane
minimalContinuumBuildsR126 continuum finiteLane = record
  { R126.LiteralBalabanSchwingerStressRecovery.finiteMeasureLane = finiteLane
  ; R126.LiteralBalabanSchwingerStressRecovery.literalFiniteMeasuresConverge =
      literalFiniteMeasuresConverge continuum
  ; R126.LiteralBalabanSchwingerStressRecovery.literalSchwingerBelongsToContinuumMeasure =
      literalSchwingerBelongsToContinuumMeasure continuum
  }

minimalFiniteMeasureAndOSBuildR457 :
  ∀ {trajectory split}
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
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation} →
  MinimalContinuumSchwingerAttachment S Y group →
  R125.LiteralFiniteMeasureStressLane stressLane →
  R127.OSLiteralSchwingerWeld Y group →
  R457.SourceNativeContinuumAndOS stressLane
minimalFiniteMeasureAndOSBuildR457 continuum finiteLane osWeld = record
  { R457.SourceNativeContinuumAndOS.sameFamilyRecovery = record
      { R128.SameFamilyOSStressRecovery.schwingerRecovery =
          minimalContinuumBuildsR126 continuum finiteLane
      ; R128.SameFamilyOSStressRecovery.osWeld = osWeld
      }
  }

minimalPrimitiveSourceInputsBuildR457 :
  ∀ {trajectory split}
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
    (selected : R119.CanonicalMetricSelectedStressWeld
      domain representation coordinate) →
  (densityAnchor : R122.DensityAnchoredCanonicalMetricStress selected) →
  R124.BalabanDensityLiteralFiniteMeasureWeld
    {trajectory = trajectory} {split = split} {inputs = inputs}
    Y group →
  MinimalContinuumSchwingerAttachment S Y group →
  R127.OSLiteralSchwingerWeld Y group →
  let metricLane = r114AndR119BuildR120 selected
      stressLane = r120AndR122BuildR123 metricLane densityAnchor
  in R457.SourceNativeContinuumAndOS stressLane
minimalPrimitiveSourceInputsBuildR457
    selected densityAnchor measureWeld continuum osWeld =
  let metricLane = r114AndR119BuildR120 selected
      stressLane = r120AndR122BuildR123 metricLane densityAnchor
      finiteLane = r123AndR124BuildR125 stressLane measureWeld
  in minimalFiniteMeasureAndOSBuildR457 continuum finiteLane osWeld

record CasimirMinimalR457SourceNativeBoundary : Set where
  constructor casimir-minimal-r457-source-native-boundary
  field
    minimalContinuumBuildsR126CompilerOwned : Bool
    minimalPrimitiveSourceInputsBuildR457CompilerOwned : Bool
    fullPinnedYangMillsConstructionRequiredForCasimirR457 : Bool
    pinnedMassGapPackageRequiredForCasimirR457 : Bool
    literalConstructionStillRequired : Bool
    continuumLimitStillRequired : Bool
    schwingerBelongsToContinuumMeasureStillRequired : Bool

open CasimirMinimalR457SourceNativeBoundary public

canonicalMinimalR457SourceNativeBoundary : CasimirMinimalR457SourceNativeBoundary
canonicalMinimalR457SourceNativeBoundary =
  casimir-minimal-r457-source-native-boundary
    true true false false true true true

casimirMinimalR457SourceNativeReading : String
casimirMinimalR457SourceNativeReading =
  "The Casimir/R457 stress lane does not require an inhabitant of the full PinnedYangMillsConstruction and therefore does not require the pinned Clay mass-gap/SI package. Its construction-level source input is one literal Y plus the exact continuum-limit and Schwinger-belongs-to-continuum-measure witnesses for the selected group. R114/R119/R122/R124/R127 then compile the existing R120/R123/R125/R126/R128/R457 packaging chain."
