module DASHI.Physics.Closure.NSPeriodicGeometricDepletionRejectionStatus where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Fail-closed ledger for the proposed geometric-depletion manuscripts.
--
-- These constructors distinguish an open analytic bridge from an argument that
-- is unusable as written.  No rejected claim is exported as a proposition, and
-- none can promote an official harmonic gate.
------------------------------------------------------------------------

data ClaimDisposition : Set where
  notEstablished : ClaimDisposition
  invalidAsWritten : ClaimDisposition
  requiresQuantitativeThreshold : ClaimDisposition
  unrelatedToPeriodicWallI : ClaimDisposition

record GeometricDepletionRejectionLedger : Set where
  field
    topologicalCurrentExponentialDecay : ClaimDisposition
    activeDirectionRigidity : ClaimDisposition
    topologicalCurrentControlsAlignment : ClaimDisposition
    antiCongruencePreimageContradiction : ClaimDisposition
    congruenceAllocationExclusion : ClaimDisposition
    exponentiallyWeightedEnstrophyPlateau : ClaimDisposition
    approximatePreconditionerCommutator : ClaimDisposition
    convexBuildingSetPaper : ClaimDisposition

open GeometricDepletionRejectionLedger public

currentGeometricDepletionLedger : GeometricDepletionRejectionLedger
currentGeometricDepletionLedger = record
  { topologicalCurrentExponentialDecay = notEstablished
  ; activeDirectionRigidity = notEstablished
  ; topologicalCurrentControlsAlignment = notEstablished
  ; antiCongruencePreimageContradiction = invalidAsWritten
  ; congruenceAllocationExclusion = invalidAsWritten
  ; exponentiallyWeightedEnstrophyPlateau = requiresQuantitativeThreshold
  ; approximatePreconditionerCommutator = unrelatedToPeriodicWallI
  ; convexBuildingSetPaper = unrelatedToPeriodicWallI
  }

T3ExponentialDecayLevel : ProofLevel
T3ExponentialDecayLevel = conditional

activeVorticityDirectionRigidityLevel : ProofLevel
activeVorticityDirectionRigidityLevel = conditional

topologicalCurrentAlignmentBridgeLevel : ProofLevel
topologicalCurrentAlignmentBridgeLevel = conditional

antiCongruenceExclusionLevel : ProofLevel
antiCongruenceExclusionLevel = conjectural

allocationExclusionLevel : ProofLevel
allocationExclusionLevel = conjectural

weightedSuperlinearODEUnconditionalPlateauLevel : ProofLevel
weightedSuperlinearODEUnconditionalPlateauLevel = conditional

geometricDepletionOfficialInputInhabited : Bool
geometricDepletionOfficialInputInhabited = false

geometricDepletionGateRegression :
  geometricDepletionOfficialInputInhabited ≡ false
geometricDepletionGateRegression = refl

geometricDepletionRejectionStatusLevel : ProofLevel
geometricDepletionRejectionStatusLevel = machineChecked
