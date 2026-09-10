module DASHI.Law.SensibLawWoogarooLegalPriorityRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooPreservationRoadmapExact as Roadmap
import DASHI.Law.SensibLawWoogarooEPBC8575DecisionConsumerMatrixExact as EPBC
import DASHI.Law.SensibLawWoogarooAdmissibleFactorsWrongTypeAtomBridgeExact as AFW

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
  "controlled-action identity; ss 18/18A matters; delegate/deadline; Lot 9999 SP292760; 162 ha referral area; 136 ha impact area; SHG 136 ha direct plus 26 ha indirect Koala-habitat impact; habitat score 7; Koala scat/food-tree evidence; connectivity score 2; >500 ha connectivity map; 136 ha critical-habitat impact map; SHG significant-impact conclusion"
  "2026 final-PD delta: final action/clearing geometry; retained habitat; avoidance/alternatives; complete residual-impact treatment; final offsets; conservation-advice/recovery-plan treatment; response to submissions and any changed assumptions since 2019"
  "SHG consultant conclusion is not a Commonwealth finding; 2019 referral state is not automatically unchanged 2026 final-PD state; significant habitat impact is not automatic Part 9 refusal"
  "historical significant-impact and habitat facts materially pay the merits input but cannot by themselves determine the current approval/refusal answer without the final-state statutory record"
  "perform a 2019-to-2026 final-PD delta audit and compile the atom-level Part 9 refusal/conditions/offset matrix"

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
  "9281/2024/OW is an approved vegetation-clearing/earthworks/stormwater works object; the same project has a historical 136 ha habitat-score-7 Koala impact map, food-tree/scat evidence and >500 ha connectivity surface"
  "exact approved 9281 clearing polygon and conditions; current commencement/threat chronology; exact current wildlife/habitat intersection; evidence of likely significant detrimental effect"
  "2019 EPBC impact geometry is not 9281 works geometry; works approval is not commencement; clearing entitlement is not the s 102 detrimental-effect conclusion"
  "approval/habitat status cannot determine the interim-order test without exact current conduct, geometry, timing and likely effect"
  "acquire the 9281 clearing plans and works chronology now; intersect them with current same-parcel habitat/species evidence and prepare the s 102 package concurrently"

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
