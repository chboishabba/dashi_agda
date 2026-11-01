module DASHI.Culture.AmyEskridgeForensicAcquisitionPriorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquisition
import DASHI.Culture.AmyEskridgeAcquisitionProofSearchExact as Acquire

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: FORENSIC ACQUISITION PRIORITY
--
-- This is a lawful evidence-routing owner. It prioritizes records by their
-- ability to discriminate competing case interpretations, not by how dramatic
-- a hypothesis appears. Absence of a publicly located record is not evidence
-- of suppression or foul play.
--
-- Snowball rule: records may be found and retained opportunistically, but they
-- re-enter the investigation only through the exact existing acquisition
-- target and dependency graph. Acquisition order is not conclusion order.
------------------------------------------------------------------------

data PriorityBand : Set where
  firstBand : PriorityBand
  secondBand : PriorityBand
  thirdBand : PriorityBand

data ForensicQuestion : Set where
  deathMechanism : ForensicQuestion
  deathManner : ForensicQuestion
  intrusionOccurrence : ForensicQuestion
  intrusionChronology : ForensicQuestion
  actorIdentity : ForensicQuestion
  researchLink : ForensicQuestion

record PrioritizedAcquisition : Set where
  constructor prioritized-acquisition
  field
    targetName : String
    priority : PriorityBand
    discriminates : ForensicQuestion
    lawfulOnly : Bool
    publicNonLocationIsNotKnownAbsence : Bool
    nonLocationIsNotEvidenceOfSuppression : Bool

open PrioritizedAcquisition public

autopsyPriority : PrioritizedAcquisition
autopsyPriority =
  prioritized-acquisition
    "autopsy / postmortem examination record"
    firstBand deathMechanism true true true

toxicologyPriority : PrioritizedAcquisition
toxicologyPriority =
  prioritized-acquisition
    "toxicology record"
    firstBand deathMechanism true true true

ballisticsPriority : PrioritizedAcquisition
ballisticsPriority =
  prioritized-acquisition
    "firearm / ballistics / GSR evidence"
    firstBand deathMechanism true true true

policePriority : PrioritizedAcquisition
policePriority =
  prioritized-acquisition
    "police incident / calls-for-service records"
    firstBand intrusionOccurrence true true true

apartmentPriority : PrioritizedAcquisition
apartmentPriority =
  prioritized-acquisition
    "apartment-management records"
    secondBand intrusionChronology true true true

originalMediaPriority : PrioritizedAcquisition
originalMediaPriority =
  prioritized-acquisition
    "original media and metadata"
    secondBand intrusionChronology true true true

exPartnerPriority : PrioritizedAcquisition
exPartnerPriority =
  prioritized-acquisition
    "ex-partner witness account"
    secondBand intrusionOccurrence true true true

------------------------------------------------------------------------
-- Exact same-target weld to the already-authoritative acquisition owner.
-- This replaces the earlier string/string + Bool compatibility shim.
------------------------------------------------------------------------

record ExactExistingAcquisitionLink
    (existingTarget : Acquisition.AcquisitionTarget)
    (priorityTarget : PrioritizedAcquisition) : Set where
  constructor exact-existing-acquisition-link
  field
    exactTargetNameIdentity :
      Acquisition.targetName existingTarget ≡ targetName priorityTarget

open ExactExistingAcquisitionLink public

autopsyExistingAcquisitionLink :
  ExactExistingAcquisitionLink Acquire.autopsyTarget autopsyPriority
autopsyExistingAcquisitionLink = exact-existing-acquisition-link refl

toxicologyExistingAcquisitionLink :
  ExactExistingAcquisitionLink Acquire.toxicologyTarget toxicologyPriority
toxicologyExistingAcquisitionLink = exact-existing-acquisition-link refl

ballisticsExistingAcquisitionLink :
  ExactExistingAcquisitionLink Acquire.ballisticsTarget ballisticsPriority
ballisticsExistingAcquisitionLink = exact-existing-acquisition-link refl

policeExistingAcquisitionLink :
  ExactExistingAcquisitionLink Acquire.policeReportTarget policePriority
policeExistingAcquisitionLink = exact-existing-acquisition-link refl

apartmentExistingAcquisitionLink :
  ExactExistingAcquisitionLink Acquire.apartmentManagementTarget apartmentPriority
apartmentExistingAcquisitionLink = exact-existing-acquisition-link refl

originalMediaExistingAcquisitionLink :
  ExactExistingAcquisitionLink Acquire.originalMediaMetadataTarget originalMediaPriority
originalMediaExistingAcquisitionLink = exact-existing-acquisition-link refl

exPartnerExistingAcquisitionLink :
  ExactExistingAcquisitionLink Acquire.exPartnerTarget exPartnerPriority
exPartnerExistingAcquisitionLink = exact-existing-acquisition-link refl

record ForensicPriorityBoundary : Set where
  constructor forensic-priority-boundary
  field
    dramaticHypothesisRaisesPriorityByItself : Bool
    forensicRecordsPrecedeCulpritInference : Bool
    intrusionEvidenceAutomaticallyDeterminesDeathManner : Bool
    antigravityNoveltyAutomaticallyCreatesResearchLink : Bool
    lawfulPrimaryRecordAcquisitionPreferred : Bool
    knownAbsentClosesOnlyExactBranch : Bool
    existingAcquisitionOwnerRemainsAuthoritative : Bool
    outOfOrderForensicAcquisitionMayBeRetained : Bool
    retainedRecordAutomaticallyPaysDependentAssessment : Bool

canonicalForensicPriorityBoundary : ForensicPriorityBoundary
canonicalForensicPriorityBoundary =
  forensic-priority-boundary false true false false true true true true false
