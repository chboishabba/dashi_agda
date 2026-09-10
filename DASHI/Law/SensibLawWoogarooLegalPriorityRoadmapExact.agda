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

qldS13Priority : LegalPriorityCoordinate
qldS13Priority = legal-priority-coordinate
  sameParcelCriticalHabitat
  consumerPaymentOpen
  "Nature Conservation Act 1992 (Qld) s 13 critical-habitat consumer for the exact Springview/Woogaroo parcel"
  "same-project exact-parcel habitat-function evidence: Lot 9999 SP292760; mostly remnant vegetation; Koala food trees/scats; Woogaroo/Opossum Creek function; SHG connectivity score 2 and >500 ha connectivity surface; habitat score 7; future fragmentation/development pressure; broader Scenic/Peninsula/Bellevue and official-corridor context"
  "identify the relevant viable protected-wildlife population/native-wildlife community; prove statutory essentiality and consequence of severance/loss; obtain current expert treatment of SHG's recovery-value-0/site-not-viable reasoning"
  "EPBC Koala-guideline critical habitat is not Queensland s 13 critical habitat; habitat score 7, occurrence and connectivity are not statutory essentiality; observer-selected FrogID is not expert validation"
  "same-parcel habitat function now survives the coarse projection, but the NCA consumer still requires the essentiality relation to the viable population/community; SHG's adverse recovery analysis must be retained and stress-tested"
  "move from discovery to legal/ecological sufficiency: have counsel/ecologist test essentiality using the exact Springview habitat/function object and current landscape evidence"

qldS102Priority : LegalPriorityCoordinate
qldS102Priority = legal-priority-coordinate
  interimRestraint
  consumerPaymentOpen
  "Nature Conservation Act ss 102-107 interim conservation-order consumer"
  "9281/2024/OW is approved by negotiated decision for Kalina Village 2 Stages 1-16 and expressly covers vegetation clearing, earthworks and stormwater. The supplied 20 March 2026 negotiated approved-plan carrier A12705838 now pays plan-scale extent-of-work geometry, bushfire-management vegetation-clearing extents, bushland-management zone, Open Space/environmental-corridor interfaces, O'Dwyers Gully/Opossum Creek context and tree-retention/removal interface. The negotiated decision separately carries the Commonwealth/Condition 6(a) prestart dependency. Same-project ecology supplies the historical 136 ha habitat-score-7 Koala impact, food-tree/scat evidence and >500 ha connectivity surface."
  "likely-significant-detrimental-effect evidence under the current s 102 consumer; current process/execution chronology; Condition 6(a) satisfaction and prestart records; current habitat/wildlife evidence sufficient to connect the approved threatening process to the qualifying wildlife/habitat/area. Machine-precise GIS and later LiDAR can strengthen the causal/spatial account but are not textual statutory prerequisites."
  "perfect spatial overlap is not an s 102 element; lack of perfect overlap does not foreclose s 102; s 103(2) permits an order relating to land even when the wildlife or habitat is not within that land; prior s 13 classification is not a universal prerequisite because s 102(a) separately covers threatened or near threatened wildlife; approval is not commencement; clearing entitlement is not the significant-detrimental-effect conclusion"
  "the relevant factorisation is process -> qualifying ecological object -> likely significant detrimental effect -> Ministerial opinion/order discretion. Geometry is evidence for process identity, causal relation, likely effect and targeting, not a freestanding statutory overlap threshold."
  "use A12705838 now as the approved threatening-process geometry; prioritise current execution/Condition 6(a)/prestart evidence and ecological likely-effect analysis. Defer LiDAR as an evidence-refinement lane rather than a prerequisite."

qldS49Priority : LegalPriorityCoordinate
qldS49Priority = legal-priority-coordinate
  permanentProtection
  consumerPaymentOpen
  "Nature Conservation Act s 49 compulsory nature-refuge route"
  "source-paid statutory mechanism and substantially stronger exact-parcel ecological evidence"
  "sufficient s 13 critical-habitat or area-of-major-interest basis; exact parcels/tenure; refuge suitability; agreement/history predicates; executive initiation record"
  "qualifying ecology or s 13 evidence is not the executive declaration and does not compel selection of this mechanism"
  "ecological value and even an essentiality case cannot factor directly to completed permanent protection without the executive/tenure predicates"
  "prepare parcel/tenure/suitability/procedure behind the live s 13 work so the permanent-protection request can activate quickly"

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
    qldS13Second : Bool
    qldS102Third : Bool
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
--
-- This is a bounded inventory statement, not a claim that an absent carrier
-- does not exist publicly. It records only what is present in the supplied
-- conversation/library corpus after a fresh title/content search.
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
