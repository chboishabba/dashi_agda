module DASHI.Law.SensibLawWoogarooLegalPriorityRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooPreservationRoadmapExact as Roadmap
import DASHI.Law.SensibLawWoogarooEPBC8575DecisionConsumerMatrixExact as EPBC
import DASHI.Law.SensibLawWoogarooAdmissibleFactorsWrongTypeAtomBridgeExact as AFW
import DASHI.Law.SensibLawWoogarooS102StatutorySpatialRelationExact as S102Statute

------------------------------------------------------------------------
-- WOOGAROO LEGAL-ONLY PRIORITY ROADMAP
------------------------------------------------------------------------

data LegalPriority : Set where
  immediateFederalDecision : LegalPriority
  sameParcelCriticalHabitat : LegalPriority
  interimRestraint : LegalPriority
  permanentProtection : LegalPriority
  exemptionAudit : LegalPriority
  enforcementBackstop : LegalPriority

data PriorityState : Set where
  sourcePaid : PriorityState
  consumerPaymentOpen : PriorityState
  decisionPending : PriorityState
  conditionalBackstop : PriorityState

record LegalPriorityCoordinate : Set where
  constructor legal-priority-coordinate
  field
    priority : LegalPriority
    state : PriorityState
    exactConsumer : String
    admittedFacts : String
    missingAtoms : String
    wrongTypeBoundary : String
    factorsThroughBoundary : String
    nextAction : String

open LegalPriorityCoordinate public

federal8575Priority : LegalPriorityCoordinate
federal8575Priority = legal-priority-coordinate
  immediateFederalDecision
  consumerPaymentOpen
  "EPBC 2019/8575 Part 9 approval/refusal decision due 1 October 2026"
  "controlled-action identity; ss 18/18A matters; delegate/deadline; Lot 9999 SP292760; 162 ha referral area; 136 ha impact area; SHG 136 ha direct plus 26 ha indirect Koala-habitat impact; habitat score 7; Koala scat/food-tree evidence; connectivity score 2; >500 ha connectivity map; 136 ha critical-habitat impact map; SHG Koala significant-impact conclusion; SHG proposition that approximately 136 ha GHFF foraging-habitat removal is likely to adversely impact habitat critical to survival; s 95B publication notice proving 1,786 comments and later publication of the PD/comments summary"
  "substantive 2026 Preliminary Documentation carrier/attachments; final action/clearing geometry; retained habitat; avoidance/alternatives; complete Koala/GHFF residual-impact treatment; final offsets; conservation-advice/recovery-plan treatment; actual summary/response to 1,786 submissions; any changed assumptions since 2019"
  "publication notice is not substantive final PD; comment count is not response adequacy; SHG consultant conclusion is not a Commonwealth finding; 2019 referral state is not automatically unchanged 2026 state; significant habitat impact is not automatic Part 9 refusal"
  "historical habitat/significant-impact propositions and publication facts materially pay merits inputs but cannot determine the live approval/refusal answer without the substantive final-state record and consumer-specific statutory reasoning"
  "first obtain the substantive final-PD/comment-response carriers, then perform the 2019-to-2026 atom-level Part 9 refusal/conditions/offset delta audit"

qldS102Priority : LegalPriorityCoordinate
qldS102Priority = legal-priority-coordinate
  interimRestraint
  consumerPaymentOpen
  "Nature Conservation Act ss 102-107 interim conservation-order consumer"
  "9281/2024/OW and A12705838 pay the approved vegetation-clearing/earthworks process and plan-scale geometry; Koala is qualifying threatened wildlife; same-project SHG ecology supplies occurrence, habitat-function, fragmentation and serious-effect evidence; Ipswich Council separately records local Koala activity and corridor function in the Woogaroo Creek system."
  "current independent ecological opinion applying s 12/s 102 to the approved/current project; current Condition 6(a)/prestart/commencement state; likely magnitude, duration and reversibility of detrimental effect; mitigation effectiveness"
  "perfect overlap is not an s 102 element; prior formal critical-habitat identification is not required for the separate threatened-wildlife gateway; approval is not commencement; federal significant impact is not automatically Queensland likely significant detrimental effect"
  "process -> qualifying threatened wildlife/habitat/area -> likely significant detrimental effect -> Ministerial opinion. Geometry, local activity and project ecology are evidence inputs, not substitutes for the statutory opinion."
  "highest-alpha Queensland action: obtain a focused independent ecological opinion and current execution records now, before irreversible works"

qldS13Priority : LegalPriorityCoordinate
qldS13Priority = legal-priority-coordinate
  sameParcelCriticalHabitat
  consumerPaymentOpen
  "Nature Conservation Act s 13 definitional essentiality consumer, feeding s 102 Ministerial opinion, s 120H conservation-plan reasoning, regulation-based identification and s 49 nature-refuge reasoning"
  "same-project habitat function; Koala food trees/scats; Woogaroo/Opossum connectivity; >500 ha project connectivity surface; Council local activity/corridor evidence; regional genetic/population structure evidence; current Queensland endangered status"
  "identify the relevant viable population/community; resolve local population/cluster identity; calculate the without-Springview persistence/connectivity counterfactual; identify which operative statutory mechanism should use the evidence"
  "s 13 is a definition, not a standalone application/declaration mechanism; EPBC critical habitat, corridor mapping, activity scores or regional cluster labels do not themselves identify formal NCA critical habitat or prove essentiality"
  "habitat evidence cannot determine statutory essentiality without the viable-population relation; even a strong s 13 factual case still needs an operative Ministerial/conservation-plan/regulation/s 49 route to produce legal effect"
  "run in parallel with s 102: acquire existing Ipswich monitoring/population evidence first, resolve the SEQ-03/SEQ-West label relation, then seek expert population/essentiality analysis"

qldS49Priority : LegalPriorityCoordinate
qldS49Priority = legal-priority-coordinate
  permanentProtection
  consumerPaymentOpen
  "Nature Conservation Act s 49 compulsory nature-refuge route"
  "s 49 text is source-paid; exact-parcel ecological evidence and the s 13 definition can inform the required Ministerial opinion"
  "failed agreement with relevant landholders; Ministerial opinion that the area is/includes critical habitat or an area of major interest and should be a nature refuge; exact parcels/tenure; objections process; Governor in Council regulation"
  "a strong s 13 essentiality case is not a standalone declaration and does not pay the failed-agreement or executive prerequisites of s 49"
  "ecological essentiality cannot factor directly to a completed permanent-protection outcome without the s 49 procedural/executive predicates"
  "prepare tenure/agreement/suitability evidence behind the live s 102 and population-essentiality work"

exemptionAuditPriority : LegalPriorityCoordinate
exemptionAuditPriority = legal-priority-coordinate
  exemptionAudit
  consumerPaymentOpen
  "exact Queensland planning/vegetation/koala exemption or grandfathering applicable to current Springview components"
  "2019 referral states a proponent-understood Planning Regulation 2017 urban-purpose/urban-area vegetation-clearing exemption theory for least-concern/of-concern vegetation, identifies protected-plants high-risk mapping and no public-notification requirement; later approval chain is identified through LAP/ADP/OW objects"
  "exact historical/current exemption instruments and transition rules; vegetation-class predicates; temporal, parcel, stage and variation scope; whether later operational works inherit the relied-upon exemption"
  "proponent legal characterisation is not adjudicated current scope; mapped habitat is not a prohibition where a valid exemption applies; no-public-notification status does not establish validity or invalidity"
  "historical legal position and approval history cannot determine current exemption coverage without the exact instrument/transition/parcel join"
  "recover and test the exact exemption authority against every current ADP/operational-works component in parallel"

enforcementPriority : LegalPriorityCoordinate
enforcementPriority = legal-priority-coordinate
  enforcementBackstop
  conditionalBackstop
  "EPBC s 475 / NCA restraint or enforcement consumer"
  "source-paid enforcement mechanisms; local works objects, federal pending-decision chronology and same-project habitat-impact evidence are available for monitoring"
  "exact threatened/actual conduct; geometry/timing; approval/permit/condition status; exact contravention/offence/restraint basis; standing/procedure"
  "environmental harm, significant habitat impact, approval existence or clearing entitlement is not automatically a statutory contravention/offence"
  "harm and habitat evidence do not factor to enforcement availability without an exact threatened or breached legal obligation"
  "keep conditional; if works become imminent, immediately map exact conduct to exact legal controls before selecting relief"

record LegalOnlyPriorityPolicy : Set where
  constructor legal-only-priority-policy
  field
    federalDecisionFirst : Bool
    qldS102Second : Bool
    qldS13ParallelThird : Bool
    qldS49Fourth : Bool
    exemptionAuditParallel : Bool
    enforcementConditional : Bool
    ashBartyOnCriticalPath : Bool
    politicalPartyAlignmentPaysLegalElement : Bool

canonicalLegalOnlyPriorityPolicy : LegalOnlyPriorityPolicy
canonicalLegalOnlyPriorityPolicy = legal-only-priority-policy
  true true true true true true false false

data AdvocacyInterestCreatesLegalElement : Set where
data PoliticalAlignmentCreatesStatutoryPayment : Set where
data CelebrityAttentionCreatesPreservationOutcome : Set where

advocacyInterestDoesNotCreateLegalElement : AdvocacyInterestCreatesLegalElement → ⊥
advocacyInterestDoesNotCreateLegalElement ()

politicalAlignmentDoesNotCreateStatutoryPayment : PoliticalAlignmentCreatesStatutoryPayment → ⊥
politicalAlignmentDoesNotCreateStatutoryPayment ()

celebrityAttentionDoesNotCreatePreservationOutcome : CelebrityAttentionCreatesPreservationOutcome → ⊥
celebrityAttentionDoesNotCreatePreservationOutcome ()

------------------------------------------------------------------------
-- CURRENT CORPUS VERIFICATION — 11 SEPTEMBER 2026
------------------------------------------------------------------------

record CurrentCorpusVerification : Set where
  constructor current-corpus-verification
  field
    finalPDPublicationNoticePresent : Bool
    substantive2026PDPresent : Bool
    actual1786CommentResponsePresent : Bool
    negotiated9281DecisionPresent : Bool
    negotiated9281ApprovedPlansPresent : Bool
    negotiated9281PlanGeometryRead : Bool
    verificationNote : String

currentCorpusVerification : CurrentCorpusVerification
currentCorpusVerification = current-corpus-verification
  true
  false
  false
  true
  true
  true
  "Fresh conversation+Library search confirms that 2019-8575-Final-PD.pdf is the one-page s 95B(2) publication notice, not the substantive 2026 Preliminary Documentation. The actual 1,786-comment summary/response is not present in the supplied corpus. By contrast, A12705835 and A12705838 are present and have already been read as the 20 March 2026 negotiated 9281 decision notice and negotiated approved plan set."
