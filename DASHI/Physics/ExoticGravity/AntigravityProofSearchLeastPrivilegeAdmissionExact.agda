module DASHI.Physics.ExoticGravity.AntigravityProofSearchLeastPrivilegeAdmissionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentSearchHypergraphExact as Hyper
import DASHI.Physics.ExoticGravity.AntigravityConstraintInformedBundleDesignExact as Design

------------------------------------------------------------------------
-- OPTIMIZED STAGE -> EXISTING LEAST-PRIVILEGE SEARCH MODALITY
------------------------------------------------------------------------

modalityForStage : Design.BundleStage → Hyper.SearchModality
modalityForStage Design.sourceGeometryStage = Hyper.physicalMeasurement
modalityForStage Design.phaseProbeStage = Hyper.perturbAndMeasure
modalityForStage Design.ordinaryModelStage = Hyper.calibrationExperiment
modalityForStage Design.scalingReplicationStage = Hyper.independentReplication
modalityForStage Design.theoryComparisonStage = Hyper.repositoryProofReuse

record AdmittedBundleStage (stage : Design.BundleStage) : Set where
  constructor admitted-bundle-stage
  field
    modality : Hyper.SearchModality
    modalityMatches : modality ≡ modalityForStage stage
    disposition : Least.RouteDisposition
    dispositionMatches : disposition ≡ Hyper.routeDisposition modality

open AdmittedBundleStage public

sourceGeometryAdmission : AdmittedBundleStage Design.sourceGeometryStage
sourceGeometryAdmission = admitted-bundle-stage
  Hyper.physicalMeasurement refl Least.admitted refl

phaseProbeAdmission : AdmittedBundleStage Design.phaseProbeStage
phaseProbeAdmission = admitted-bundle-stage
  Hyper.perturbAndMeasure refl Least.admitted refl

ordinaryModelAdmission : AdmittedBundleStage Design.ordinaryModelStage
ordinaryModelAdmission = admitted-bundle-stage
  Hyper.calibrationExperiment refl Least.admitted refl

scalingReplicationAdmission : AdmittedBundleStage Design.scalingReplicationStage
scalingReplicationAdmission = admitted-bundle-stage
  Hyper.independentReplication refl Least.admitted refl

theoryComparisonReuse : AdmittedBundleStage Design.theoryComparisonStage
theoryComparisonReuse = admitted-bundle-stage
  Hyper.repositoryProofReuse refl Least.redirectedReuse refl

------------------------------------------------------------------------
-- Admission means the route is allowed for proof search; it is not a receipt
-- that the move was executed, succeeded, or produced kernel authority.
------------------------------------------------------------------------

record AntigravityLeastPrivilegeBoundary : Set where
  constructor antigravity-least-privilege-boundary
  field
    currentPhysicalSourceMoveIsAdmitted : Bool
    phasePerturbationMoveIsAdmitted : Bool
    ordinaryCalibrationMoveIsAdmitted : Bool
    replicationMoveIsAdmitted : Bool
    theoryComparisonPrefersRepositoryReuse : Bool
    admittedMoveEqualsExecutedExperiment : Bool
    admittedMoveEqualsSuccessfulReceipt : Bool
    admittedMoveCreatesKernelAuthority : Bool
    rejectedPromotionShortcutRemainsRejected : Bool

canonicalAntigravityLeastPrivilegeBoundary : AntigravityLeastPrivilegeBoundary
canonicalAntigravityLeastPrivilegeBoundary =
  antigravity-least-privilege-boundary
    true true true true true false false false true
