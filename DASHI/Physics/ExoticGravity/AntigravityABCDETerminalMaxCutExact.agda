{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityABCDETerminalMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.GRQFTLocalizedAnisotropicRepulsiveShellExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityTimelikeEnergySharpActiveStressCriterionExact as Active
import DASHI.Physics.Foundations.PositiveGActiveStressWeakFieldMetricExact as Metric
import DASHI.Physics.ExoticGravity.AntigravityDeviceMetricObservableCompilerExact as Observables
import DASHI.Physics.ExoticGravity.AntigravityDeviceOpticalMetricDiscriminatorExact as Experiment
import DASHI.Physics.ExoticGravity.AntigravitySearchNonGeometricOppositeExact as Opposite

------------------------------------------------------------------------
-- A -> E TERMINAL MAX-CUT
--
-- A  source construction / physical-realisation contract
-- B  exact active-stress sign criterion
-- C  exact selected spherical weak-field geometry solve
-- D  one-geometry four-channel projection
-- E  same-object, reversal-aware experimental discrimination
--
-- The mathematical path is closed through the selected weak-field sector.
-- The remaining source leaf is physical realisation/calibration of a device
-- stress tensor with the required values.  The nonlinear compact Einstein/TOV
-- completion remains a stronger geometry theorem, not a prerequisite for the
-- already-closed weak-field A->E experiment lane.
------------------------------------------------------------------------

stageASourceContract : Source.LocalizedAnisotropicRepulsiveShellWitness
stageASourceContract = Source.canonicalLocalizedAnisotropicRepulsiveShellWitness

stageBActiveStressCriterion :
  Source.activeStressDensity Source.boundaryZone ≡ - Source.rho Source.boundaryZone
stageBActiveStressCriterion = refl

stageCWeakFieldMetricSolve : Metric.WeakFieldMetricSolveBoundary
stageCWeakFieldMetricSolve = Metric.canonicalWeakFieldMetricSolveBoundary

stageDFourChannelProjection : Observables.DeviceMetricObservableBoundary
stageDFourChannelProjection = Observables.canonicalDeviceMetricObservableBoundary

stageESameObjectExperiment : Experiment.AntigravityDeviceDiscriminatorBoundary
stageESameObjectExperiment = Experiment.canonicalAntigravityDeviceDiscriminatorBoundary

nonGeometricOppositeFirewall : Opposite.AntigravityNonGeometricOppositeBoundary
nonGeometricOppositeFirewall = Opposite.canonicalAntigravityNonGeometricOppositeBoundary

record AntigravityABCDEFrontier : Set where
  constructor antigravity-a-b-c-d-e-frontier
  field
    stageASourceShapeConstructed : Bool
    stageBActiveStressSignMathClosed : Bool
    stageCWeakFieldInteriorSolved : Bool
    stageCWeakFieldExteriorSolved : Bool
    stageCWeakFieldSurfaceMatched : Bool
    stageCOutwardAccelerationDerived : Bool
    stageDFourChannelProjectionCompiled : Bool
    stageESameObjectComparatorCompiled : Bool
    oppositeCouplingNotPromotedToOppositeGeometry : Bool

    physicalDeviceStressRealisationStillOpen : Bool
    apparatusCalibrationStillOpen : Bool
    empiricalReplicationStillOpen : Bool
    fullNonlinearCompactEinsteinSolveStillOpen : Bool
    fullTOVConservationStillOpen : Bool

canonicalAntigravityABCDEFrontier : AntigravityABCDEFrontier
canonicalAntigravityABCDEFrontier =
  antigravity-a-b-c-d-e-frontier
    true true true true true true true true true
    true true true true true

------------------------------------------------------------------------
-- Promotion boundary: "complete A->E" means the mathematical/compiler lane
-- is complete in the selected weak-field sector.  It does not manufacture the
-- material source, calibration, replication, or nonlinear exact metric.
------------------------------------------------------------------------

record AntigravityABCDEPromotionBoundary : Set where
  constructor antigravity-a-b-c-d-e-promotion-boundary
  field
    weakFieldMathematicalLaneClosed : Bool
    fullPhysicalDeviceDemonstrated : Bool
    weightOnlyObservationProvesMetric : Bool
    opticalOnlyObservationProvesAntigravity : Bool
    physicalDeviceStressRealisationStillOpen : Bool
    fullNonlinearCompactEinsteinSolveStillOpen : Bool

canonicalAntigravityABCDEPromotionBoundary : AntigravityABCDEPromotionBoundary
canonicalAntigravityABCDEPromotionBoundary =
  antigravity-a-b-c-d-e-promotion-boundary
    true false false false true true
