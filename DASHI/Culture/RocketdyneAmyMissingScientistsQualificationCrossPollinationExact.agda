{-# OPTIONS --safe #-}
module DASHI.Culture.RocketdyneAmyMissingScientistsQualificationCrossPollinationExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.RocketdyneBerylliumQualificationEvidenceExact as Rocket
import DASHI.Physics.Propulsion.Rocketdyne1974MeasuredResultsExact as Data
import DASHI.Culture.AmyEskridgeHAL5AntigravitySourceEntitlementExact as Amy
import DASHI.Culture.MissingDeceasedCombinedRocketScramjetVehicleBidiExact as Vehicle

------------------------------------------------------------------------
-- CROSS-POLLINATION, NOT COMMON-PROGRAMME INFERENCE
--
-- (1) Historical Rocketdyne hardware qualification is a different kind of
--     evidence from a speaker's sourced discussion of speculative physics.
-- (2) A plausible use in the combined rocket/scramjet architecture identifies
--     engineering requirements, NOT historical membership or cooperation.
-- (3) An individual scientist's death or missing-record status cannot be
--     inferred from historical capability overlap.
-- NASA-CR-140308: https://ntrs.nasa.gov/citations/19740027091
-- NASA RAMPT: https://techport.nasa.gov/projects/93946
------------------------------------------------------------------------

data EvidenceStratum : Set where
  testedHardware sourcedHistoricalTalk applicationFit
  candidateOrganisationLink independentlyVerifiedLink : EvidenceStratum

data Mechanism : Set where
  chemicalCombustion thermalAndStructuralQualification
  proposedGravityModification : Mechanism

record ProvenanceWeld : Set where
  constructor provenance-weld
  field
    leftSource : String
    rightSource : String
    sharedObjectKey : String
    independenceEvidence : String
    directParticipationEvidence : String
    validationEvidence : String

record CrossDomainCandidate : Set where
  constructor candidate
  field
    archivalProgramme : Rocket.HistoricalProgramme
    sourceArticle : Rocket.TestArticle
    sourceStratum : EvidenceStratum
    destinationStratum : EvidenceStratum
    sourceMechanism : Mechanism
    destinationMechanism : Mechanism
    application : String
    unpaidBridge : String

berylliumRocketToCombinedVehicle : CrossDomainCandidate
berylliumRocketToCombinedVehicle =
  candidate Rocket.berylliumINTEREGEN Rocket.durabilityEngine
    testedHardware applicationFit
    thermalAndStructuralQualification chemicalCombustion
    "source-indexed RCS engine qualification as comparator for rocket-side hardware"
    "Requires common mission envelopes, pressure, mixture ratio, materials, joints, controls and vehicle-system test evidence"

amyTalkToPropulsionResearch : CrossDomainCandidate
amyTalkToPropulsionResearch =
  candidate Rocket.berylliumINTEREGEN Rocket.offLimitsEngine
    sourcedHistoricalTalk applicationFit
    proposedGravityModification chemicalCombustion
    "2018 HAL5 historical antigravity presentation as a hypothesis catalogue"
    "No measured force, mechanism equivalence or Rocketdyne participation established"

-- The constructors establish a formal type-level separation, not a factual
-- assessment of any person's circumstances.
hardwareNotTalk : testedHardware ≡ sourcedHistoricalTalk → ⊥
hardwareNotTalk ()

fitNotVerifiedLink : applicationFit ≡ independentlyVerifiedLink → ⊥
fitNotVerifiedLink ()

gravityProposalNotCombustion : proposedGravityModification ≡ chemicalCombustion → ⊥
gravityProposalNotCombustion ()

record QualificationTransferFrontier : Set where
  constructor qualification-frontier
  field
    historicArticle : Rocket.Observation
    contemporarySource : String
    thermalEnvelopeOverlap : String
    contaminationAndMaintenanceOverlap : String
    brazeVsBimetallicJointComparison : String
    repeatedStartAndFatigueComparison : String
    componentScaleAndDutyCycleComparison : String
    missingMeasurement : String

ramptComparator : QualificationTransferFrontier
ramptComparator =
  qualification-frontier Rocket.durabilityExposure
    "NASA RAMPT; https://techport.nasa.gov/projects/93946"
    "Not established: separately quantify chamber wall temperatures, heat flux and cooling architecture"
    "Not established: align contaminants, maintenance schedule and damage inspections"
    "Not established: historical injector-to-beryllium braze versus modern graded/bimetallic joint"
    "Not established: compare cycle definitions, loading spectra, starts and accumulated thermal exposure"
    "Not established: normalize geometry, thrust class, propellants and pressure"
    "Raw time histories, engineering drawings, material revisions, inspection and acceptance records"

-- Directly use the already admitted Amy receipt and real-object owner.
amySourced2018Talk : Amy.HAL5TalkSourceReceipt
amySourced2018Talk = Amy.canonicalHAL5TalkSourceReceipt

rocketAndAirbreatherRemainSeparate : Bool
rocketAndAirbreatherRemainSeparate = Vehicle.rocketOxidizerAndScramjetAirAreDifferentInputs

record InvestigativeNonPromotion : Set where
  constructor non-promotion
  field
    commonResearchTopicProvesCollaboration : Bool
    qualificationResultProvesAntigravity : Bool
    technicalOverlapProvesTargetingOrDeathCause : Bool
    discussionIsIndependentPhysicalValidation : Bool
    unresolvedArchiveMeansHistoricalNonexistence : Bool
    campaignResultProvesUnlimitedServiceLife : Bool
    legitimateNewAcquisitionRoute : Bool

canonicalNonPromotion : InvestigativeNonPromotion
canonicalNonPromotion =
  non-promotion false false false false false false true

-- Material/valve outcomes remain source-specific; neither is a gravity test.
archivalNozzleDamage : Data.ComponentOutcome
archivalNozzleDamage = Data.nozzleHighTemperatureDamage

archivalValveFailure : Data.ComponentOutcome
archivalValveFailure = Data.moogContamination

archivalSteadyPerformance : Data.DecimalResult
archivalSteadyPerformance = Data.unsaturatedIsp
