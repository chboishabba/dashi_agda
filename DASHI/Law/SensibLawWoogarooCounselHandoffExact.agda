module DASHI.Law.SensibLawWoogarooCounselHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooPreservationRoadmapExact as Roadmap

------------------------------------------------------------------------
-- WOOGAROO COUNSEL HANDOFF
--
-- This is a lawyer-facing issue/gap carrier. It does not promote DASHI's
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
  "EPBC 2019/8575: determine the strongest lawful route to put a decision-grade refusal/conditions case before the authorised delegate before the current decision deadline."
  "Project identity, controlled-action status, controlling species/community, authorised delegate, 1 October 2026 deadline, neighbouring-project proponent evidence on critical koala habitat/connectivity, Scenic/Peninsula common 675 ha landscape analysis, local development approvals, and current offset/additionality questions are now source-paid at their own fibres."
  "Validate the operative Part 9 decision criteria and mandatory considerations; advise what material can still be lodged; identify whether further-information, extension, reconsideration, merits/review or preservation steps remain available; and identify which cumulative-fragmentation/offset propositions are legally material to the actual decision consumer."
  "Springview final-PD same-object action/clearing polygon; impacted versus retained habitat; significance conclusions; avoidance and alternatives; residual impacts; exact offset calculations and management assumptions; conservation-advice/recovery-plan correspondence; response-to-submissions material."
  "1 October 2026"
  false

qldCriticalHabitatCounselIssue : CounselHandoffIssue
qldCriticalHabitatCounselIssue = counsel-handoff-issue
  Roadmap.qldCriticalHabitat
  testElementSufficiency
  highAlphaParallel
  "Nature Conservation Act 1992 (Qld) s 13: test whether the exact Woogaroo/Springfield habitat can satisfy the statutory critical-habitat definition."
  "The landscape-function case is materially advanced: Scenic and Peninsula are analysed by the proponent against the same approximately 675 ha contiguous landscape; Bellevue proponent material recognises Woogaroo Creek connectivity and restoration lag; official corridor context is source-paid; historical wooded-cover evidence exists; neighbouring-project critical-koala-habitat/removal figures are source-paid; and present-day observer occurrence evidence is preserved separately."
  "Identify the administrative/procedural vehicle for an s 13 case, the evidentiary threshold for 'essential' and 'viable population', whether corridor/pinch-point function can satisfy that test, and the best species/community-specific proof structure. Stress-test both the supporting and defeating construction."
  "Exact Springview project/cadastral polygon joined to primary habitat-function evidence showing why this particular habitat, rather than threatened-species presence or regional connectivity in the abstract, is essential to conservation of a viable protected-wildlife population or native-wildlife community."
  "before irreversible clearing; run in parallel with federal and s 102 work"
  false

qldInterimCounselIssue : CounselHandoffIssue
qldInterimCounselIssue = counsel-handoff-issue
  Roadmap.qldInterim
  identifyProceduralVehicle
  highAlphaParallel
  "NCA ss 102-107: assess an interim conservation-order request directed at the concrete Springview clearing/works sequence."
  "The statutory mechanism is source-paid and 9281/2024/OW supplies an approved operational-works object expressly covering earthworks, vegetation clearing and stormwater; 9293/2024/OW separately covers road/drainage/stormwater/earthworks. The broader habitat/corridor evidence is now materially stronger."
  "Advise who can request action, required form/evidence, whether threatened wildlife independently activates s 102 without prior s 13 identification, whether an approved local clearing entitlement can constitute the relevant threatening process before commencement, what imminence/detrimental-effect showing is required, and review options if the request is not acted on."
  "9281/2024/OW approved clearing drawing and exact stage footprint; current commencement/works chronology; exact habitat/species intersection; evidence sufficient to support likely significant detrimental effect."
  "before vegetation clearing or other irreversible works commence"
  false

qldNatureRefugeCounselIssue : CounselHandoffIssue
qldNatureRefugeCounselIssue = counsel-handoff-issue
  Roadmap.qldPermanent
  validateStatutoryConstruction
  highAlphaParallel
  "NCA s 49: assess realistic availability of compulsory nature-refuge protection for the relevant parcels."
  "Statutory s 49 power is source-paid, and the ecological/corridor case is materially stronger, but the qualifying s 13/area-of-major-interest and parcel/tenure predicates remain open."
  "Advise procedural prerequisites, third-party initiation/request capacity, tenure/compensation implications, what evidence can establish suitability and area-of-major-interest status, and whether another permanent-protection mechanism is faster or stronger."
  "Exact parcel/tenure; s 13 critical-habitat or area-of-major-interest basis; suitability/management intent; agreement history; executive initiation pathway."
  "prepare behind the s 13 lane; do not wait to identify procedure until after the federal decision"
  false

planningExemptionCounselIssue : CounselHandoffIssue
planningExemptionCounselIssue = counsel-handoff-issue
  Roadmap.planningExemption
  obtainPrimaryMaterial
  highAlphaParallel
  "Identify the exact Springview planning/koala exemption or grandfathering instrument and its present scope across the actual approval chain."
  "Council material records mapped koala habitat together with an exempted/approved development outcome. The local chain now includes 6243/2023/LAP, 4272/2020/ADP, 5547/2020/ADP, 7477/2022/ADP, 9281/2024/OW and 9293/2024/OW."
  "Identify the precise statutory/instrument basis for exemption or grandfathering; approval dates; parcel/stage scope; lapse/change/variation rules; whether operational works inherit the same protection; and whether any later component or variation falls outside it."
  "Primary state/local approval instruments; historical Springfield Structure Plan or other exemption authority; variations/extensions; stage-specific plans; reasons/conditions linking the approvals."
  "before relying on ordinary planning/koala prohibition arguments and before any enforcement theory assumes the local approvals are invalid"
  false

offsetCounterfactualCounselIssue : CounselHandoffIssue
offsetCounterfactualCounselIssue = counsel-handoff-issue
  Roadmap.federal8575
  testElementSufficiency
  highAlphaParallel
  "Test the legal relevance and evidentiary sufficiency of the proposed-offset counterfactual, including maturity/restoration lag, additionality, existing protection and overlap with prior obligations."
  "Public-source material identifies proposed offset candidates by name/area at a secondary-source level; the impact landscape has stronger evidence of mature connected habitat and active development pressure; Bellevue proponent material expressly recognises restoration lag; broader Mt Mort material indicates substantial existing conservation management; and 'Avonvale' presents a same-name identity/possible-overlap acquisition issue."
  "Advise which offset-policy/Part 9 propositions require exact proof; whether without-offset risk of loss, prior protection, prior EPBC obligations, rehabilitation maturity and functional equivalence are legally material; and what documentary disclosure should be sought from the proponent/department."
  "Exact lot/plan and GIS polygon for each offset; existing covenants/VCAs/Land for Wildlife/EPBC offset obligations/restoration grants; vegetation condition and age; baseline risk of loss; management actions; time-to-functional-equivalence; exact identity resolution for Avonvale/Esk/Mt Walker West."
  "urgent enough to feed the federal merits lane before decision; otherwise preserve for review/conditions scrutiny"
  false

enforcementCounselIssue : CounselHandoffIssue
enforcementCounselIssue = counsel-handoff-issue
  Roadmap.enforcementBackstop
  identifyEnforcementRoute
  conditionalBackstop
  "Map any imminent or proposed conduct to an exact EPBC/NCA contravention before seeking injunction/enforcement relief."
  "EPBC s 475 and Queensland NCA enforcement-order machinery exist as statutory routes; local works approvals and the federal decision chronology are separately preserved."
  "Advise standing, exact cause/contravention, evidentiary preservation, urgency, costs/undertaking risks, and whether judicial review/declaratory relief is more appropriate."
  "Exact threatened conduct; exact legal obligation/condition/prohibition; commencement chronology; approval status; proof of breach or threatened breach."
  "activate only if facts satisfy the legal trigger"
  false

------------------------------------------------------------------------
-- Current counsel sequencing.
------------------------------------------------------------------------

record CounselExecutionPolicy : Set where
  constructor counsel-execution-policy
  field
    federalMeritsFirst : Bool
    s13AndS102Concurrent : Bool
    offsetAuditFeedsFederal : Bool
    planningExemptionParallel : Bool
    s49PreparedBehindS13 : Bool
    enforcementOnlyOnExactTrigger : Bool

canonicalCounselExecutionPolicy : CounselExecutionPolicy
canonicalCounselExecutionPolicy =
  counsel-execution-policy true true true true true true

------------------------------------------------------------------------
-- No-promotion firewalls.
------------------------------------------------------------------------

data DashReconstructionEqualsLegalAdvice : Set where
data CounselReviewAutomaticallyPaysMissingFact : Set where
data ProBonoRepresentationCreatesMerits : Set where
data LawyerInvolvementCreatesStatutoryStanding : Set where
data ApprovedLocalWorksEqualsFederalPermission : Set where
data OffsetConcernEqualsOffsetInvalidity : Set where

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

localWorksDoNotCreateFederalPermission : ApprovedLocalWorksEqualsFederalPermission → ⊥
localWorksDoNotCreateFederalPermission ()

offsetConcernDoesNotProveInvalidity : OffsetConcernEqualsOffsetInvalidity → ⊥
offsetConcernDoesNotProveInvalidity ()

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
