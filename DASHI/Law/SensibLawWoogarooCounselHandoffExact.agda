module DASHI.Law.SensibLawWoogarooCounselHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooPreservationRoadmapExact as Roadmap

------------------------------------------------------------------------
-- WOOGAROO COUNSEL HANDOFF
--
-- Lawyer-facing issue/gap carrier. DASHI reconstruction is not legal advice,
-- an agency finding, an adjudicated fact, or a realised preservation outcome.
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
  "EPBC 2019/8575: stress-test the live Part 9 decision using the project's own referral-era ecology and identify the legally material 2019-to-2026 delta before the current decision deadline."
  "Controlled-action status; ss 18/18A controlling matters; delegate/deadline; Lot 9999 SP292760; 162 ha referral area; 136 ha stated impact area; SHG 136 ha direct plus 26 ha indirect Koala-habitat impact; habitat score 7/10; Koala scat and food-tree evidence; habitat-connectivity score 2; rendered >500 ha connectivity map; rendered 136 ha critical-habitat impact map; SHG conclusion that clearing/functional loss of 136 ha would significantly impact Koala habitat critical to survival; SHG separate conclusion that removal of approximately 136 ha GHFF foraging habitat is likely to adversely impact habitat critical to survival; s 95B(2) publication notice proving 1,786 public comments and later publication of the PD/comments summary."
  "Validate operative Part 9 criteria/mandatory considerations; determine what weight attaches to the proponent consultant's own Koala and GHFF habitat-critical adverse-impact conclusions; require/stress-test reconciliation of >500 ha connectivity and future-fragmentation evidence against SHG's recovery-value-0/isolation reasoning; distinguish habitat-critical adverse impact from population/recovery conclusions; identify what material may still be lodged and what review/evidence-preservation steps should occur before decision."
  "First acquire the substantive 2026 Preliminary Documentation volumes/attachments because the uploaded file named Final-PD is only the one-page publication notice; then perform the delta audit: final action/clearing geometry; retained habitat; avoidance/alternatives; complete Koala/GHFF residual-impact treatment; final offsets and management assumptions; conservation-advice/recovery-plan treatment; actual summary/response to the 1,786 public comments and any changed ecology/assumptions since 2019."
  "1 October 2026"
  false

qldCriticalHabitatCounselIssue : CounselHandoffIssue
qldCriticalHabitatCounselIssue = counsel-handoff-issue
  Roadmap.qldCriticalHabitat
  testElementSufficiency
  highAlphaParallel
  "Nature Conservation Act 1992 (Qld) s 13: test whether the exact Springview/Woogaroo habitat satisfies the statutory essentiality definition, without collapsing the older EPBC Koala-guideline label into the Queensland legal test."
  "Same-project habitat-function evidence is now strong: Lot 9999 SP292760; mostly remnant vegetation; recognised Koala food trees; Koala scats; Woogaroo/Opossum Creek adjacency and habitat/connectivity function; SHG connectivity score 2; Plan 5 >500 ha connected-habitat surface; habitat score 7; future surrounding development/fragmentation identified by SHG. Broader Scenic/Peninsula/Bellevue and official-corridor evidence remains supporting context."
  "Identify the actual procedural vehicle and evidentiary threshold for 'essential' and 'viable population/community'; determine whether the NCA test differs materially from the older EPBC recovery-value analysis; stress-test SHG's adverse recovery-value-0/site-not-viable reasoning against its own connectivity findings, subsequent development pressure, current corridor evidence and current ecology."
  "Species/community-specific viable-population essentiality proposition; expert treatment of severance/loss consequences; current spatial/ecological evidence sufficient to resolve the tension between connectivity/function and the 2019 adverse recovery-value conclusion."
  "before irreversible clearing; run in parallel with federal and s 102 work"
  false

qldInterimCounselIssue : CounselHandoffIssue
qldInterimCounselIssue = counsel-handoff-issue
  Roadmap.qldInterim
  identifyProceduralVehicle
  highAlphaParallel
  "NCA ss 102-107: assess an interim conservation-order request directed at the concrete Springview/Kalina Village 2 clearing and works sequence."
  "A user-supplied Ipswich City Council application export now directly records 9281/2024/OW as Kalina Village 2 Stages 1 to 16 - Earthworks, Clearing Vegetation and Stormwater; Progress 'Decided'; Stage/Decision 'Approved - Negotiated Decision Approved'; Application Type 'Operational Works'; uses including Operational Works - Civil, Operational Works - Environment, Earthworks, Stormwater Drainage and Vegetation Clearing; Assessment Officer Philip Tian; submitted 20 August 2024; decided 20 March 2026; Public Notification Required 'No'. It associates the application with 30 Parkside Drive, 7001 Mur Boulevard, 7006 Panorama Drive and 1 Telopea Way, Springfield. The assessment-stage table records confirmation, information-request/response and change-representation stages, with change representations completed on 20 March 2026. The same Springview project has a 2019 proponent ecology surface mapping 136 ha of habitat-score-7 Koala impact, food trees/scats and >500 ha connectivity."
  "Advise who may request action, required form/evidence, whether threatened wildlife can engage s 102 without prior s 13 identification, whether an approved but not proved-commenced clearing entitlement can be the relevant threatening process, what evidence is sufficient for likely significant detrimental effect, and whether any significance attaches to the planning record showing Public Notification Required 'No'."
  "The one-page Council export still does not expose the negotiated approved vegetation-clearing polygon, retained-tree/open-space geometry, conditions or commencement prerequisites. Acquire the 20 March 2026 negotiated approved plans/decision notice and current works chronology, then intersect exact works geometry with current habitat/species/corridor evidence."
  "before vegetation clearing or other irreversible works commence"
  false

qldNatureRefugeCounselIssue : CounselHandoffIssue
qldNatureRefugeCounselIssue = counsel-handoff-issue
  Roadmap.qldPermanent
  validateStatutoryConstruction
  highAlphaParallel
  "NCA s 49: assess realistic availability of compulsory nature-refuge protection for the relevant parcels."
  "Statutory s 49 power is source-paid and same-parcel ecology is now substantially stronger, but the qualifying s 13/area-of-major-interest and parcel/tenure/executive predicates remain open."
  "Advise procedural prerequisites, third-party initiation/request capacity, tenure/compensation implications, suitability evidence, agreement-history requirements and whether another permanent-protection mechanism is faster or stronger."
  "Exact parcel/tenure; s 13 critical-habitat or area-of-major-interest basis; suitability/management intent; agreement history; executive initiation pathway."
  "prepare behind the s 13 lane"
  false

planningExemptionCounselIssue : CounselHandoffIssue
planningExemptionCounselIssue = counsel-handoff-issue
  Roadmap.planningExemption
  obtainPrimaryMaterial
  highAlphaParallel
  "Identify the exact Springview planning/vegetation/koala exemption or grandfathering instrument and its present scope across the actual approval chain."
  "The 2019 referral states the proponent's then-understood Planning Regulation 2017 urban-purpose/urban-area clearing exemption theory for least-concern/of-concern regulated vegetation. The 9281/2024/OW Council export now directly records an Operational Works approval including Vegetation Clearing, a negotiated approval decision dated 20 March 2026 and Public Notification Required 'No', together with the associated Springfield properties. Later Council material and the LAP/ADP/OW chain record approved/exempted outcomes."
  "Identify exact historical/current statutory instruments, transition provisions, vegetation-class predicates, approval dates, parcel/stage scope, lapse/change/variation rules, the legal basis for Public Notification Required 'No', and whether later operational works inherit the same exemption. Treat the proponent's 2019 legal characterisation and the Council application-status export as evidence of their respective records, not as a judicial determination of current exemption validity."
  "Primary state/local approval instruments and reasons; exact exemption/grandfathering authority; transition instruments; negotiated decision notice; approved plans/conditions; variations/extensions; stage-specific plans."
  "before relying on ordinary planning/koala prohibition arguments or any enforcement theory that assumes local invalidity"
  false

offsetCounterfactualCounselIssue : CounselHandoffIssue
offsetCounterfactualCounselIssue = counsel-handoff-issue
  Roadmap.federal8575
  testElementSufficiency
  highAlphaParallel
  "Test proposed-offset adequacy against the now-source-paid impact-side baseline, including additionality, existing protection, maturity/restoration lag and functional equivalence."
  "The Springview impact side now has proponent evidence of habitat score 7, 136 ha direct plus 26 ha indirect Koala-habitat impact, a consultant significant-impact conclusion, and a separate 136 ha GHFF foraging-habitat adverse-critical-habitat proposition. Public/secondary material identifies candidate offset names/areas; Bellevue evidence supports restoration-lag analysis; regional conservation context and the Avonvale identity collision remain acquisition leads."
  "Advise which offset-policy/Part 9 propositions require exact proof and whether baseline risk of loss, prior protection/obligations, maturity, temporal lag and functional equivalence must be demonstrated against this impact-side habitat/function baseline."
  "Exact lot/plan and GIS polygon for each final offset; existing covenants/VCAs/Land for Wildlife/EPBC obligations/restoration funding; current vegetation condition/maturity; lawful baseline risk of loss; management actions; time-to-functional-equivalence; substantive final 2026 offset calculations and conditions."
  "urgent enough to feed the federal merits lane before decision; otherwise preserve for review/conditions scrutiny"
  false

frogSurveyCounselIssue : CounselHandoffIssue
frogSurveyCounselIssue = counsel-handoff-issue
  Roadmap.qldCriticalHabitat
  testElementSufficiency
  highAlphaParallel
  "Assess whether the 2019 amphibian survey limitations and current Opossum/Woogaroo occurrence evidence create a material contemporary survey/update issue."
  "SHG identifies Woogaroo and Opossum Creeks as having potential frog habitat values and states rainfall before its threatened-frog survey was not optimal under the EPBC threatened-frog survey guidelines for accurately understanding acid-frog populations. A 2026 observer-selected FrogID Tusked Frog record near the Opossum Creek interface is preserved but remains pending validation."
  "Ask an ecologist whether the 2019 survey design/target taxa/weather remains adequate for current decision-making and whether current targeted survey or expert review is warranted; advise only if any resulting evidence is legally material to the federal/NCA consumers."
  "Expert validation/current survey evidence; exact spatial relation to project/works; no promotion from observer selection or suboptimal old survey conditions to species-presence fact."
  "supporting evidence lane; accelerate if expert validation or imminent works make it material"
  false

enforcementCounselIssue : CounselHandoffIssue
enforcementCounselIssue = counsel-handoff-issue
  Roadmap.enforcementBackstop
  identifyEnforcementRoute
  conditionalBackstop
  "Map any imminent or proposed conduct to an exact EPBC/NCA contravention before seeking injunction/enforcement relief."
  "EPBC s 475 and Queensland NCA enforcement-order machinery exist as statutory routes; local works approvals, federal chronology and same-project ecology are separately preserved. The Council export proves 9281/2024/OW is decided/negotiated-approved but does not prove commencement."
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
data SHGConclusionEqualsCommonwealthFinding : Set where
data EPBCCriticalHabitatEqualsNCA13CriticalHabitat : Set where
data ReferralStateEqualsFinalPDState : Set where
data PublicationNoticeEqualsSubstantiveFinalPD : Set where
data CommentCountEqualsResponseAdequacy : Set where
data ApplicationLocationMapEqualsApprovedClearingPolygon : Set where
data PublicNotificationNotRequiredEqualsNoConsultationOccurred : Set where

dashReconstructionDoesNotBecomeLegalAdvice : DashReconstructionEqualsLegalAdvice → ⊥
dashReconstructionDoesNotBecomeLegalAdvice ()

counselReviewDoesNotCreateMissingEvidence : CounselReviewAutomaticallyPaysMissingFact → ⊥
counselReviewDoesNotCreateMissingEvidence ()

proBonoStatusDoesNotCreateMerits : ProBonoRepresentationCreatesMerits → ⊥
proBonoStatusDoesNotCreateMerits ()

lawyerInvolvementDoesNotCreateStanding : LawyerInvolvementCreatesStatutoryStanding → ⊥
lawyerInvolvementDoesNotCreateStanding ()

localWorksDoNotCreateFederalPermission : ApprovedLocalWorksEqualsFederalPermission → ⊥
localWorksDoNotCreateFederalPermission ()

offsetConcernDoesNotProveInvalidity : OffsetConcernEqualsOffsetInvalidity → ⊥
offsetConcernDoesNotProveInvalidity ()

shgConclusionDoesNotBecomeAgencyFinding : SHGConclusionEqualsCommonwealthFinding → ⊥
shgConclusionDoesNotBecomeAgencyFinding ()

epbcCriticalDoesNotBecomeNCA13 : EPBCCriticalHabitatEqualsNCA13CriticalHabitat → ⊥
epbcCriticalDoesNotBecomeNCA13 ()

referralStateDoesNotBecomeFinalPDState : ReferralStateEqualsFinalPDState → ⊥
referralStateDoesNotBecomeFinalPDState ()

publicationNoticeDoesNotBecomeFinalPD : PublicationNoticeEqualsSubstantiveFinalPD → ⊥
publicationNoticeDoesNotBecomeFinalPD ()

commentCountDoesNotPayResponseAdequacy : CommentCountEqualsResponseAdequacy → ⊥
commentCountDoesNotPayResponseAdequacy ()

applicationMapDoesNotBecomeClearingPolygon : ApplicationLocationMapEqualsApprovedClearingPolygon → ⊥
applicationMapDoesNotBecomeClearingPolygon ()

noNotificationFlagDoesNotProveNoConsultation : PublicNotificationNotRequiredEqualsNoConsultationOccurred → ⊥
noNotificationFlagDoesNotProveNoConsultation ()

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
