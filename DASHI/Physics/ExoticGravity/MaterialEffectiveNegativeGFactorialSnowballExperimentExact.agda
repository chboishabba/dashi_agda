module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGFactorialSnowballExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScientificWallProgressionExact as Progress
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGDiscriminatorCutsetExact as Cutset
import DASHI.Physics.ExoticGravity.LiTorrSourceAttributedOrdinaryGREvaluationExact as Attribution

------------------------------------------------------------------------
-- FACTORIAL EXPERIMENT + SNOWBALL ACQUISITION
--
-- Experimental cells may be collected opportunistically. This owner projects
-- their observed coordinates into the canonical ScientificWallAcquisitionState
-- from the receipt-indexed progression owner. It does not define a second
-- payment scheduler and it does not promote acquisition into payment.
------------------------------------------------------------------------

data SourceAmplitudeLevel : Set where
  sourceLow sourceHigh : SourceAmplitudeLevel

data MaterialRegime : Set where
  normalRegime superconductingRegime : MaterialRegime

record FactorialCell : Set where
  constructor factorial-cell
  field
    sourceAmplitude : SourceAmplitudeLevel
    materialRegime : MaterialRegime
    apparatusIdentity : String
    geometryRevision : String
    calibrationRevision : String
    measurementSource : Attribution.RoleBoundSource
    measurementSourceRoleIsExperimental :
      Attribution.role measurementSource ≡ Attribution.experimentalMeasurement
    measurementSourceSameApparatus :
      Attribution.entitlement measurementSource ≡ Attribution.sameApparatusMeasurement
    cellCarrier : String
    residualCarrier : String

open FactorialCell public

record SnowballAcquisitionState : Set where
  constructor snowball-acquisition-state
  field
    acquiredCells : List FactorialCell
    sourceAmplitudeAxisObserved : Bool
    materialRegimeAxisObserved : Bool
    sameSourceIdentityObserved : Bool
    sameGeometryObserved : Bool
    ordinaryBackgroundClosureObserved : Bool
    fieldSignObserved : Bool
    independentReplicationObserved : Bool
    modelClassSeparationObserved : Bool
    outOfOrderCellsRetained : Bool

open SnowballAcquisitionState public

boolAnd : Bool → Bool → Bool
boolAnd false _ = false
boolAnd true b = b

------------------------------------------------------------------------
-- Canonical acquisition projection.
--
-- The factorial surface is downstream of source reconstruction, so it cannot
-- claim mass-current or stress-energy acquisition merely from having cells.
-- It may retain evidence for the independent source/material axes, model-class
-- separation, and replication/identity coordinates when the corresponding
-- observations are actually present.
------------------------------------------------------------------------

projectToCanonicalAcquisition :
  SnowballAcquisitionState → Progress.ScientificWallAcquisitionState
projectToCanonicalAcquisition s =
  Progress.scientific-wall-acquisition-state
    false
    false
    (boolAnd (sourceAmplitudeAxisObserved s) (materialRegimeAxisObserved s))
    (modelClassSeparationObserved s)
    (boolAnd (independentReplicationObserved s)
      (boolAnd (sameSourceIdentityObserved s) (sameGeometryObserved s)))

-- Deliberate firewall: acquisition does not advance the payment state by itself.
snowballAcquisitionDoesNotAdvancePaymentByItself :
  SnowballAcquisitionState → Progress.ScientificWallPaymentState
snowballAcquisitionDoesNotAdvancePaymentByItself _ = Progress.currentWallState

record FactorialSnowballBoundary : Set where
  constructor factorial-snowball-boundary
  field
    outOfOrderAcquisitionMayBeRetained : Bool
    acquiredCellCountEqualsDependencyPayment : Bool
    sourceAxisObservationEqualsSourceAxisPayment : Bool
    materialAxisObservationEqualsMaterialAxisPayment : Bool
    factorialDatasetAutomaticallySeparatesModelClasses : Bool
    factorialDatasetAutomaticallyProvesNegativeEffectiveG : Bool
    sourceAttributionRolesSurvivePerCell : Bool
    canonicalScientificWallAcquisitionStateReused : Bool
    canonicalScientificWallSchedulerRemainsAuthoritative : Bool

canonicalFactorialSnowballBoundary : FactorialSnowballBoundary
canonicalFactorialSnowballBoundary =
  factorial-snowball-boundary true false false false false false true true true

-- Alignment with the existing discriminator cutset: these are the exact
-- experiment coordinates this dataset is intended to inform when corresponding
-- receipt-bearing evidence exists.
requiredCutset : Cutset.MaterialEffectiveNegativeGCutset
requiredCutset = Cutset.canonicalMaterialEffectiveNegativeGCutset
