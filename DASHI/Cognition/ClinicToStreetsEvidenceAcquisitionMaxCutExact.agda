module DASHI.Cognition.ClinicToStreetsEvidenceAcquisitionMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalIdentificationFamiliesExact as Identification
import DASHI.Cognition.ClinicToStreetsCausalProvenanceMaxCutExact as Max

------------------------------------------------------------------------
-- FINAL ACQUISITION CUT: REUSE THE CANONICAL CAUSAL SPINE
--
-- The earlier version of this file carried a local edge-evidence checklist
-- (`sameObjectPopulation`, `temporallyOrdered`, `alternativeExplanationsAudited`,
-- `interventionOrNaturalExperiment`).  That duplicated the repository's mature
-- causal-estimand / identification-family machinery.
--
-- This revision keeps only Clinic-specific acquisition demands and source
-- status.  Actual causal payment must use the canonical generic owners:
--
--   CausalEffectEstimandExact
--     population x intervention x comparator x outcome x horizon
--
--   CausalIdentificationFamiliesExact
--     obligation-relative randomized / adjusted observational / longitudinal /
--     mediation / genetic / neural identification receipts.
--
-- An attributed reel/book claim therefore remains source provenance only.  It
-- does not instantiate an estimand, identification gate, calibrated magnitude,
-- or empirical causal effect.
------------------------------------------------------------------------

data SourceEvidenceStatus : Set where
  unacquired : SourceEvidenceStatus
  attributedSource : SourceEvidenceStatus
  sourceSupported : SourceEvidenceStatus
  independentlyReplicated : SourceEvidenceStatus

record CausalEdgeDemand (edge : Max.Edge) : Set where
  constructor causal-edge-demand
  field
    kind : Estimand.CausalEstimandKind
    preferredIdentificationFamily : Identification.CausalIdentificationFamily
    populationReference : String
    interventionReference : String
    comparatorReference : String
    outcomeReference : String
    horizonReference : String
    sourceStatus : SourceEvidenceStatus
    estimandPaid : Bool
    identificationReceiptPaid : Bool
    magnitudeCalibrated : Bool

open CausalEdgeDemand public

structuralToFamilyDemand : CausalEdgeDemand Max.structuralToFamily
structuralToFamilyDemand =
  causal-edge-demand
    Estimand.mediatedIndirectEffect
    Identification.mechanisticMediation
    "a declared situated population in which structural and family/intimate coordinates are measured on the same units"
    "specified structural/institutional exposure or intervention"
    "declared counterfactual/comparator structural condition"
    "family/intimate activation or mediation outcome"
    "declared follow-up horizon"
    attributedSource
    false false false

familyToPsychicDemand : CausalEdgeDemand Max.familyToPsychic
familyToPsychicDemand =
  causal-edge-demand
    Estimand.mediatedIndirectEffect
    Identification.mechanisticMediation
    "a declared situated population with same-unit family/intimate and psychic/affective measurements"
    "specified family/intimate exposure or mediator manipulation where ethically and scientifically admissible"
    "declared comparator family/intimate condition"
    "psychic/affective or causal-attribution outcome"
    "declared follow-up horizon"
    attributedSource
    false false false

structuralToPsychicDemand : CausalEdgeDemand Max.structuralToPsychic
structuralToPsychicDemand =
  causal-edge-demand
    Estimand.controlledDirectEffect
    Identification.adjustedObservationalComparison
    "a declared situated population with structural and psychic coordinates measured on the same units"
    "specified structural/institutional exposure"
    "declared comparator structural condition"
    "psychic/affective or causal-attribution outcome"
    "declared follow-up horizon"
    unacquired
    false false false

------------------------------------------------------------------------
-- No current empirical causal payment is manufactured from the supplied reel.
------------------------------------------------------------------------

anyCurrentIdentificationReceiptPaid : Bool
anyCurrentIdentificationReceiptPaid = false

reusesCausalEffectEstimand : Bool
reusesCausalEffectEstimand = true

reusesCausalIdentificationFamilies : Bool
reusesCausalIdentificationFamilies = true

reimplementsCausalIdentificationChecklist : Bool
reimplementsCausalIdentificationChecklist = false

attributedClaimsAreEmpiricalCausalProof : Bool
attributedClaimsAreEmpiricalCausalProof = false

------------------------------------------------------------------------
-- The generic causal owners already enforce the important firewalls.  Re-export
-- their boundaries here so the Clinic acquisition surface cannot silently drift
-- back to chronology == causation or identification-family == effect.
------------------------------------------------------------------------

inheritedEstimandBoundary : Estimand.CausalEffectEstimandBoundary
inheritedEstimandBoundary = Estimand.canonicalCausalEffectEstimandBoundary

inheritedIdentificationBoundary : Identification.CausalIdentificationFamiliesBoundary
inheritedIdentificationBoundary = Identification.canonicalCausalIdentificationFamiliesBoundary

longitudinalOrderStillDoesNotIdentifyCause :
  Identification.LongitudinalMeansCausationPermission → ⊥
longitudinalOrderStillDoesNotIdentifyCause =
  Identification.longitudinalOrderDoesNotByItselfIdentifyCause

identificationFamilyStillDoesNotProveEffect :
  Identification.IdentificationFamilyAutomaticallyProvesCausalEffectPermission → ⊥
identificationFamilyStillDoesNotProveEffect =
  Identification.identificationFamilyDoesNotAutomaticallyProveCausalEffect

identificationStillDoesNotDetermineEstimand :
  Estimand.IdentificationMeansEstimandKnownPermission → ⊥
identificationStillDoesNotDetermineEstimand =
  Estimand.identificationDoesNotDetermineEstimand

------------------------------------------------------------------------
-- Responsibility and represented-action outcomes remain distinct measurement
-- obligations.  They are not collapsed into causal identification or legal /
-- moral fault.
------------------------------------------------------------------------

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

canonicalResponsibilityMappingBoundary : ResponsibilityMappingReceipt
canonicalResponsibilityMappingBoundary =
  responsibility-mapping-receipt true false false false

canonicalActionConeEffectBoundary : ActionConeEffectReceipt
canonicalActionConeEffectBoundary =
  action-cone-effect-receipt false false false false

data ExplanatoryResponsibilityImpliesFault : Set where
explanatoryResponsibilityDoesNotEstablishFault :
  ExplanatoryResponsibilityImpliesFault → ⊥
explanatoryResponsibilityDoesNotEstablishFault ()

data RepresentedConeImpliesBehaviour : Set where
representedConeDoesNotEstablishBehaviour :
  RepresentedConeImpliesBehaviour → ⊥
representedConeDoesNotEstablishBehaviour ()

------------------------------------------------------------------------
-- Role-typed illustrative coordinates remain explicitly non-empirical.
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

data ModelCoordinateImpliesCalibratedMagnitude : Set where
modelCoordinateDoesNotEstablishCalibratedMagnitude :
  ModelCoordinateImpliesCalibratedMagnitude → ⊥
modelCoordinateDoesNotEstablishCalibratedMagnitude ()

record FinalMaxCutBoundary : Set where
  constructor final-max-cut-boundary
  field
    finiteStructurePaid : Bool
    canonicalEstimandSpineReused : Bool
    canonicalIdentificationSpineReused : Bool
    localIdentificationChecklistRetired : Bool
    causalEdgesRequireSameObjectEmpiricalPayment : Bool
    magnitudeRequiresCalibration : Bool
    responsibilityMappingRequiresIndependentReceipt : Bool
    actionConeBehaviourRequiresMeasurement : Bool
    modelNumbersRoleTyped : Bool
    moreAbstractStructureCountsAsEmpiricalProgress : Bool

canonicalFinalMaxCutBoundary : FinalMaxCutBoundary
canonicalFinalMaxCutBoundary =
  final-max-cut-boundary
    true true true true true true true true true false
