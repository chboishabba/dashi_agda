{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityMatchedControlExperimentDonorMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.ExoticGravity.LiTorrStaticNullBoundBidiExact as StaticNull

------------------------------------------------------------------------
-- MATCHED-CONTROL EXPERIMENT DONOR MAX-CUT
--
-- Cross-pollination donor: open PR #1132's matched-history laboratory
-- systematics.  We import no birthmark/history theory and make no identification
-- between that source and the CMP119 vacuum coordinate.  Only the generic
-- experimental discipline is retained:
--
--   * the candidate source-state switch is the synchronous modulation channel;
--   * conventional stress-energy and geometry are re-matched/monitored;
--   * EM, thermal, mechanical, optical and vibration/acoustic channels are
--     explicitly controlled;
--   * null preparation, calibration signal and preregistration are required;
--   * the numerical systematic floor must be closed below the target signal.
--
-- Existing-master cross-pollination: Li et al. 1997 supplies a source-backed
-- STATIC YBCO null-bound receipt.  Any candidate claiming a generic static
-- response in that regime must respect it.  The historical experiment does NOT
-- pay the same-apparatus identity, geometry, phase state, driven source switch,
-- or numerical systematics budget of a new experiment.
------------------------------------------------------------------------

sourceStateSwitchIsSynchronousModulationChannel : Bool
sourceStateSwitchIsSynchronousModulationChannel = true

conventionalStressRematchingRequired : Bool
conventionalStressRematchingRequired = true

massGeometryPositionControlRequired : Bool
massGeometryPositionControlRequired = true

electromagneticControlRequired : Bool
electromagneticControlRequired = true

thermalMechanicalOpticalVibrationControlRequired : Bool
thermalMechanicalOpticalVibrationControlRequired = true

nullPreparationChannelRequired : Bool
nullPreparationChannelRequired = true

calibrationSignalRequired : Bool
calibrationSignalRequired = true

preregisteredAnalysisRequired : Bool
preregisteredAnalysisRequired = true

numericalSystematicsBudgetStillRequired : Bool
numericalSystematicsBudgetStillRequired = true

physicalMatchedSourceSwitchStillRequired : Bool
physicalMatchedSourceSwitchStillRequired = true

empiricalReplicationStillRequired : Bool
empiricalReplicationStillRequired = true

birthmarkHistoryIdentifiedWithCMP119VacuumCoordinate : Bool
birthmarkHistoryIdentifiedWithCMP119VacuumCoordinate = false

historicalStaticYBCONullConstraintAvailable : Bool
historicalStaticYBCONullConstraintAvailable = true

candidateMustRespectHistoricalStaticYBCOBound : Bool
candidateMustRespectHistoricalStaticYBCOBound =
  StaticNull.StaticNullBoundary.staticNullConstrainsGenericStaticModels
    StaticNull.canonicalStaticNullBoundary

historicalStaticNullPaysNewSameApparatusReceipt : Bool
historicalStaticNullPaysNewSameApparatusReceipt =
  StaticNull.StaticNullBoundary.historicalNullMayPayNewSameApparatusReceipt
    StaticNull.canonicalStaticNullBoundary

exactHistoricalGeometryMayReplaceNewDeviceGeometry : Bool
exactHistoricalGeometryMayReplaceNewDeviceGeometry = false

record MatchedControlExperimentFrontier : Set where
  constructor matched-control-experiment-frontier
  field
    synchronousSourceModulation : Bool
    conventionalStressRematching : Bool
    geometryControl : Bool
    electromagneticControl : Bool
    thermalMechanicalOpticalVibrationControl : Bool
    nullPreparation : Bool
    calibrationChannel : Bool
    preregistration : Bool
    historicalStaticConstraintAvailable : Bool
    historicalStaticNullPaysNewSameApparatus : Bool
    historicalGeometryReplacesNewGeometry : Bool
    numericalSystematicsBudgetOpen : Bool
    physicalMatchedSwitchOpen : Bool
    replicationOpen : Bool
    birthmarkTheoryPromotedToCMP119Source : Bool

canonicalMatchedControlExperimentFrontier : MatchedControlExperimentFrontier
canonicalMatchedControlExperimentFrontier =
  matched-control-experiment-frontier
    true true true true true true true true
    true false false
    true true true false

historicalStaticNullPaysNewSameApparatusReceiptIsFalse :
  historicalStaticNullPaysNewSameApparatusReceipt ≡ false
historicalStaticNullPaysNewSameApparatusReceiptIsFalse = refl

exactHistoricalGeometryMayReplaceNewDeviceGeometryIsFalse :
  exactHistoricalGeometryMayReplaceNewDeviceGeometry ≡ false
exactHistoricalGeometryMayReplaceNewDeviceGeometryIsFalse = refl

birthmarkHistoryIdentifiedWithCMP119VacuumCoordinateIsFalse :
  birthmarkHistoryIdentifiedWithCMP119VacuumCoordinate ≡ false
birthmarkHistoryIdentifiedWithCMP119VacuumCoordinateIsFalse = refl
