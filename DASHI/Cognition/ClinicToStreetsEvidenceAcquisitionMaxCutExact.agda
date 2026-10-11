module DASHI.Cognition.ClinicToStreetsEvidenceAcquisitionMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Cognition.ClinicToStreetsCausalProvenanceMaxCutExact as Max

------------------------------------------------------------------------
-- FINAL STRUCTURAL MAX-CUT: EVIDENCE-ACQUISITION CONTRACTS
--
-- The finite causal-DAG structure is already paid.  This owner makes the
-- remaining external obligations explicit instead of adding another abstract
-- narrative layer.  A model edge, magnitude, responsibility map, or action-cone
-- change becomes empirical only when a correspondingly typed receipt is paid.
------------------------------------------------------------------------

data EvidenceGrade : Set where
  unacquired attributedSource sourceSupported independentlyReplicated : EvidenceGrade

record EdgeEvidenceReceipt (e : Max.Edge) : Set where
  constructor edge-evidence-receipt
  field
    grade : EvidenceGrade
    sameObjectPopulation : Bool
    temporallyOrdered : Bool
    alternativeExplanationsAudited : Bool
    interventionOrNaturalExperiment : Bool

record MagnitudeCalibrationReceipt (e : Max.Edge) : Set where
  constructor magnitude-calibration-receipt
  field
    calibrated : Bool
    uncertaintyRepresented : Bool
    heldOutValidated : Bool

record ResponsibilityMappingReceipt : Set where
  constructor responsibility-mapping-receipt
  field
    explanatoryOnly : Bool
    independentlyMeasured : Bool
    moralFaultClaimed : Bool
    legalFaultClaimed : Bool

record ActionConeEffectReceipt : Set where
  constructor action-cone-effect-receipt
  field
    representedAvailabilityMeasured : Bool
    behaviourMeasured : Bool
    underlyingCarrierDeleted : Bool
    intentEstablished : Bool

------------------------------------------------------------------------
-- Current source-relative status for the supplied reel/book tranche.
--
-- The transcript supplies attributed propositions, not independently validated
-- causal-edge magnitudes or behavioural-action-cone measurements.
------------------------------------------------------------------------

structuralToFamilyCurrent : EdgeEvidenceReceipt Max.structuralToFamily
structuralToFamilyCurrent =
  edge-evidence-receipt attributedSource false false false false

familyToPsychicCurrent : EdgeEvidenceReceipt Max.familyToPsychic
familyToPsychicCurrent =
  edge-evidence-receipt attributedSource false false false false

structuralToPsychicCurrent : EdgeEvidenceReceipt Max.structuralToPsychic
structuralToPsychicCurrent =
  edge-evidence-receipt unacquired false false false false

structuralToFamilyMagnitudeCurrent : MagnitudeCalibrationReceipt Max.structuralToFamily
structuralToFamilyMagnitudeCurrent =
  magnitude-calibration-receipt false false false

canonicalResponsibilityMappingBoundary : ResponsibilityMappingReceipt
canonicalResponsibilityMappingBoundary =
  responsibility-mapping-receipt true false false false

canonicalActionConeEffectBoundary : ActionConeEffectReceipt
canonicalActionConeEffectBoundary =
  action-cone-effect-receipt false false false false

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data AttributedEdgeImpliesEmpiricalCausality : Set where
attributedEdgeDoesNotEstablishEmpiricalCausality :
  AttributedEdgeImpliesEmpiricalCausality → ⊥
attributedEdgeDoesNotEstablishEmpiricalCausality ()

data ModelCoordinateImpliesCalibratedMagnitude : Set where
modelCoordinateDoesNotEstablishCalibratedMagnitude :
  ModelCoordinateImpliesCalibratedMagnitude → ⊥
modelCoordinateDoesNotEstablishCalibratedMagnitude ()

data ExplanatoryResponsibilityImpliesFault : Set where
explanatoryResponsibilityDoesNotEstablishFault :
  ExplanatoryResponsibilityImpliesFault → ⊥
explanatoryResponsibilityDoesNotEstablishFault ()

data RepresentedConeImpliesBehaviour : Set where
representedConeDoesNotEstablishBehaviour :
  RepresentedConeImpliesBehaviour → ⊥
representedConeDoesNotEstablishBehaviour ()

------------------------------------------------------------------------
-- Role-typed model coordinates.
--
-- Equal Nat values do not identify their meanings.  This mirrors the newer
-- repository-wide number/role provenance discipline without importing numeric
-- genealogy into this older branch.
------------------------------------------------------------------------

data CoordinateRole : Set where
  representedUpstreamSalience responsibilityStructuralShare
  responsibilityIntimateShare responsibilityIndividualShare
  representedActionConeCardinality : CoordinateRole

record ModelCoordinate : Set where
  constructor model-coordinate
  field
    value : Nat
    role : CoordinateRole
    empirical : Bool

fullSalienceCoordinate : ModelCoordinate
fullSalienceCoordinate = model-coordinate 9 representedUpstreamSalience false

atomisedSalienceCoordinate : ModelCoordinate
atomisedSalienceCoordinate = model-coordinate 3 representedUpstreamSalience false

fullStructuralResponsibilityCoordinate : ModelCoordinate
fullStructuralResponsibilityCoordinate = model-coordinate 6 responsibilityStructuralShare false

atomisedIndividualResponsibilityCoordinate : ModelCoordinate
atomisedIndividualResponsibilityCoordinate = model-coordinate 7 responsibilityIndividualShare false

atomisedActionConeCoordinate : ModelCoordinate
atomisedActionConeCoordinate = model-coordinate 1 representedActionConeCardinality false

data EqualScalarImpliesSameRole : Set where
equalScalarDoesNotIdentifyRole : EqualScalarImpliesSameRole → ⊥
equalScalarDoesNotIdentifyRole ()

record FinalMaxCutBoundary : Set where
  constructor final-max-cut-boundary
  field
    finiteStructurePaid : Bool
    edgeExistenceRequiresEvidence : Bool
    magnitudeRequiresCalibration : Bool
    responsibilityMappingRequiresIndependentReceipt : Bool
    actionConeBehaviourRequiresMeasurement : Bool
    modelNumbersRoleTyped : Bool
    attributedClaimsAreEmpiricalCausalProof : Bool
    moreAbstractStructureCountsAsEmpiricalProgress : Bool

canonicalFinalMaxCutBoundary : FinalMaxCutBoundary
canonicalFinalMaxCutBoundary =
  final-max-cut-boundary true true true true true true false false
