module DASHI.Culture.AmyEskridgeForensicAcquisitionPriorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeAcquisitionProofSearchExact as Acquire

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: FORENSIC ACQUISITION PRIORITY
--
-- This is a lawful evidence-routing owner.  It prioritizes records by their
-- ability to discriminate competing case interpretations, not by how dramatic
-- a hypothesis appears.  Absence of a publicly located record is not evidence
-- of suppression or foul play.
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
    "apartment-management / access / security records"
    secondBand intrusionChronology true true true

originalMediaPriority : PrioritizedAcquisition
originalMediaPriority =
  prioritized-acquisition
    "original media and native metadata"
    secondBand intrusionChronology true true true

exPartnerPriority : PrioritizedAcquisition
exPartnerPriority =
  prioritized-acquisition
    "independent voluntary first-person witness account"
    secondBand intrusionOccurrence true true true

record ExistingAcquisitionLink : Set where
  constructor existing-acquisition-link
  field
    existingTargetName : String
    priorityTargetName : String
    sameTargetByConstruction : Bool

open ExistingAcquisitionLink public

autopsyExistingAcquisitionLink : ExistingAcquisitionLink
autopsyExistingAcquisitionLink =
  existing-acquisition-link
    "autopsy / postmortem examination record"
    "autopsy / postmortem examination record"
    true

policeExistingAcquisitionLink : ExistingAcquisitionLink
policeExistingAcquisitionLink =
  existing-acquisition-link
    "police incident / calls-for-service records"
    "police incident / calls-for-service records"
    true

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

canonicalForensicPriorityBoundary : ForensicPriorityBoundary
canonicalForensicPriorityBoundary =
  forensic-priority-boundary false true false false true true true
