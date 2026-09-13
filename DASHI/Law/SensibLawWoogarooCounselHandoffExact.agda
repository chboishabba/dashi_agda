module DASHI.Law.SensibLawWoogarooCounselHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooPreservationRoadmapExact as Roadmap

------------------------------------------------------------------------
-- WOOGAROO COUNSEL HANDOFF
--
-- This is a lawyer-facing issue/gap carrier.  It does not promote DASHI's
-- reconstruction into legal advice, a concluded legal opinion, an agency
-- finding, or an adjudicated result.
------------------------------------------------------------------------

data CounselTaskKind : Set where
  validateStatutoryConstruction : CounselTaskKind
  identifyProceduralVehicle : CounselTaskKind
  testElementSufficiency : CounselTaskKind
  identifyReviewGrounds : CounselTaskKind
  identifyEnforcementRoute : CounselTaskKind
  evidencePreservationAdvice : CounselTaskKind
  obtainPrimaryMaterial : CounselTaskKind

data CounselPriority : Set where
  urgentBeforeFederalDeadline : CounselPriority
  highAlphaParallel : CounselPriority
  conditionalBackstop : CounselPriority

record CounselHandoffIssue : Set where
  constructor counsel-handoff-issue
  field
    roadmapCoordinate : Roadmap.RoadmapCoordinate
    taskKind : CounselTaskKind
    priority : CounselPriority
    issue : String
    alreadySourcePaid : String
    counselValidationRequested : String
    evidenceResidual : String
    deadlineOrTrigger : String
    dashConclusionIsLegalAdvice : Bool

open CounselHandoffIssue public

federalDecisionCounselIssue : CounselHandoffIssue
federalDecisionCounselIssue = counsel-handoff-issue
  Roadmap.federal8575
  identifyProceduralVehicle
  urgentBeforeFederalDeadline
  "EPBC 2019/8575: determine the strongest lawful route to put a decision-grade refusal case before the authorised delegate before the current decision deadline."
  "Project identity, controlled-action status, listed controlling provisions, authorised delegate, and 1 October 2026 deadline."
  "Validate the Part 9 decision criteria/mandatory considerations; advise what material can still be lodged, whether further information/extension/reconsideration routes exist, and what review rights should be preserved."
  "Final Preliminary Documentation maps/tables, exact habitat-loss/retention calculations, alternatives, residual impacts, offsets, conservation-advice/recovery-plan treatment."
  "1 October 2026"
  false

qldCriticalHabitatCounselIssue : CounselHandoffIssue
qldCriticalHabitatCounselIssue = counsel-handoff-issue
  Roadmap.qldCriticalHabitat
  testElementSufficiency
  highAlphaParallel
  "Nature Conservation Act 1992 (Qld) s 13: test whether the exact Woogaroo/Springfield habitat can satisfy the statutory critical-habitat definition."
  "Current s 13 statutory definition plus threatened-species, remnant-habitat, corridor/connectivity and fragmentation evidence at differing source fibres."
  "Identify the administrative/procedural vehicle for an s 13 case, the evidentiary threshold for 'essential' and 'viable population', and the best species/community-specific proof structure."
  "Same-parcel habitat-function and population-essentiality receipt."
  "before irreversible clearing; parallel with federal decision"
  false

qldInterimCounselIssue : CounselHandoffIssue
qldInterimCounselIssue = counsel-handoff-issue
  Roadmap.qldInterim
  identifyProceduralVehicle
  highAlphaParallel
  "NCA ss 102-107: assess an interim conservation-order request directed at threatened clearing/works."
  "Statutory interim-conservation-order mechanism and candidate threatened wildlife/habitat evidence."
  "Advise who can request action, required form/evidence, whether threatened wildlife independently activates s 102 without prior s 13 identification, and review options if the request is not acted on."
  "Exact works/timing x wildlife/habitat x likely significant detrimental effect."
  "before works commence"
  false

qldNatureRefugeCounselIssue : CounselHandoffIssue
qldNatureRefugeCounselIssue = counsel-handoff-issue
  Roadmap.qldPermanent
  validateStatutoryConstruction
  highAlphaParallel
  "NCA s 49: assess realistic availability of compulsory nature-refuge protection for the relevant parcels."
  "Statutory s 49 power where agreement cannot be reached and the Minister considers the area critical habitat/area of major interest and suitable for declaration."
  "Advise procedural prerequisites, third-party initiation/request capacity, tenure/compensation implications, and whether another permanent-protection mechanism is faster or stronger."
  "Exact parcel/tenure, critical-habitat or area-of-major-interest basis, suitability/management intent, and agreement history."
  "parallel with federal decision and s 13 work"
  false

planningExemptionCounselIssue : CounselHandoffIssue
planningExemptionCounselIssue = counsel-handoff-issue
  Roadmap.planningExemption
  obtainPrimaryMaterial
  highAlphaParallel
  "Identify the exact Springview planning/koala exemption or grandfathering instrument and its present scope."
  "Council material demonstrates mapped koala habitat can coexist with an approved/exempted development outcome."
  "Identify approval instruments/dates, statutory basis, parcel/stage scope, lapse/change rules, and whether later variations/components remain inside the historical exemption."
  "Primary state/local approvals, exemption/grandfathering instruments, variations, extensions and stage-specific plans."
  "before relying on ordinary planning/koala prohibition arguments"
  false

enforcementCounselIssue : CounselHandoffIssue
enforcementCounselIssue = counsel-handoff-issue
  Roadmap.enforcementBackstop
  identifyEnforcementRoute
  conditionalBackstop
  "Map any imminent or proposed conduct to an exact EPBC/NCA contravention before seeking injunction/enforcement relief."
  "EPBC s 475 and Queensland NCA enforcement-order machinery exist as statutory routes."
  "Advise standing, exact cause/contravention, evidentiary preservation, urgency, costs/undertaking risks, and whether judicial review/declaratory relief is more appropriate."
  "Exact threatened conduct and exact statutory contravention/offence."
  "activate only if facts satisfy the legal trigger"
  false

------------------------------------------------------------------------
-- No-promotion firewalls.
------------------------------------------------------------------------

data DashReconstructionEqualsLegalAdvice : Set where
data CounselReviewAutomaticallyPaysMissingFact : Set where
data ProBonoRepresentationCreatesMerits : Set where
data LawyerInvolvementCreatesStatutoryStanding : Set where

dashReconstructionDoesNotBecomeLegalAdvice :
  DashReconstructionEqualsLegalAdvice → ⊥
dashReconstructionDoesNotBecomeLegalAdvice ()

counselReviewDoesNotCreateMissingEvidence :
  CounselReviewAutomaticallyPaysMissingFact → ⊥
counselReviewDoesNotCreateMissingEvidence ()

proBonoStatusDoesNotCreateMerits : ProBonoRepresentationCreatesMerits → ⊥
proBonoStatusDoesNotCreateMerits ()

lawyerInvolvementDoesNotCreateStanding : LawyerInvolvementCreatesStatutoryStanding → ⊥
lawyerInvolvementDoesNotCreateStanding ()

record CounselHandoffBoundary : Set where
  constructor counsel-handoff-boundary
  field
    legalPriorityDominatesCelebrityOutreach : Bool
    counselAskedToStressTestNotRubberStamp : Bool
    sourceAndInferenceSeparated : Bool
    proceduralVehicleTreatedAsSeparateFromMerits : Bool
    evidenceResidualsRemainOpenUntilPaid : Bool

canonicalCounselHandoffBoundary : CounselHandoffBoundary
canonicalCounselHandoffBoundary =
  counsel-handoff-boundary true true true true true
