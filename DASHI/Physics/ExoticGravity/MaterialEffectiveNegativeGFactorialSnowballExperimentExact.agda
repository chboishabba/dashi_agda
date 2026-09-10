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
-- Cross-pollinates the recent scientific-wall rule:
-- out-of-order acquisition may accumulate and be retained, while dependency
-- payment remains first-open and receipt-indexed.  This owner does not mutate
-- the canonical progression scheduler and is compatible with the stronger
-- acquisition/payment split introduced in recent PR work.
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

record FactorialPaymentEligibility : Set where
  constructor factorial-payment-eligibility
  field
    sourceAmplitudeSweepPaid : Bool
    materialRegimeSweepPaid : Bool
    sameSourceIdentityPaid : Bool
    sameGeometryPaid : Bool
    backgroundClosurePaid : Bool
    fieldSignPaid : Bool
    independentReplicationPaid : Bool
    modelClassSeparationPaid : Bool

open FactorialPaymentEligibility public

-- Deliberate firewall: a large accumulated dataset is not itself a scientific
-- wall payment.  The canonical dependency scheduler remains authoritative.
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
    canonicalScientificWallSchedulerRemainsAuthoritative : Bool

canonicalFactorialSnowballBoundary : FactorialSnowballBoundary
canonicalFactorialSnowballBoundary =
  factorial-snowball-boundary true false false false false false true true

-- Alignment with the existing discriminator cutset: these are the exact
-- experiment coordinates this dataset is intended to pay when corresponding
-- receipt-bearing evidence exists.
requiredCutset : Cutset.MaterialEffectiveNegativeGCutset
requiredCutset = Cutset.canonicalMaterialEffectiveNegativeGCutset
