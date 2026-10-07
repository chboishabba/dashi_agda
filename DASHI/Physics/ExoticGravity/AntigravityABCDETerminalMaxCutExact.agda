{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityABCDETerminalMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (1ℚ; -_)

import DASHI.Physics.Foundations.GRQFTLocalizedAnisotropicRepulsiveShellExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityTimelikeEnergySharpActiveStressCriterionExact as Active
import DASHI.Physics.Foundations.PositiveGActiveStressWeakFieldMetricExact as Metric
import DASHI.Physics.ExoticGravity.AntigravityDeviceMetricObservableCompilerExact as Observables
import DASHI.Physics.ExoticGravity.AntigravityDeviceOpticalMetricDiscriminatorExact as Experiment
import DASHI.Physics.ExoticGravity.AntigravitySearchNonGeometricOppositeExact as Opposite

------------------------------------------------------------------------
-- A -> E TERMINAL MAX-CUT
------------------------------------------------------------------------

stageASourceContract : Source.LocalizedAnisotropicRepulsiveShellWitness
stageASourceContract = Source.canonicalLocalizedAnisotropicRepulsiveShellWitness

stageBActiveStressCriterion :
  Source.activeStressDensity Source.boundaryZone ≡ - 1ℚ
stageBActiveStressCriterion = Source.boundaryActiveStressIsNegativeOne

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
