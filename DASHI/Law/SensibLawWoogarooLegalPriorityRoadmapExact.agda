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
--
-- Public-figure outreach, political alignment and general campaign narrative
-- remain optional supporting lanes.  They are not members of the shortest
-- legal path to preservation.
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
  "controlled-action identity; controlling species/community; authorised delegate; s 130(1A) extension/deadline; broader same-landscape corridor/connectivity evidence; neighbouring-project proponent critical-habitat/removal evidence; restoration-lag evidence; local development-pressure and offset-counterfactual leads"
  "2019/8575 final-PD same-object action/clearing polygon; impacted and retained habitat by controlling matter; significance reasoning; avoidance/minimisation; residual impact; offsets; conservation-advice/recovery-plan correspondence; response-to-submissions"
  "controlled action is not refusal; neighbouring-project evidence is not 2019/8575 evidence; threatened-species presence and corridor value are not the final significant-impact/Part 9 answer"
  "species lists, neighbouring critical-habitat scores, corridor evidence or development pressure cannot by themselves factor to approval/refusal"
  "recover/extract the exact 2019/8575 final Preliminary Documentation bundle and compile the atom-level Part 9 refusal/conditions/offset matrix"

qldS13Priority : LegalPriorityCoordinate
qldS13Priority = legal-priority-coordinate
  sameParcelCriticalHabitat
  consumerPaymentOpen
  "Nature Conservation Act 1992 (Qld) s 13 critical-habitat application to exact threatened Woogaroo parcels"
  "s 13 definition; proponent-side Scenic/Peninsula approximately 675 ha contiguous-landscape carrier; Bellevue/Woogaroo Creek connectivity evidence; official broader corridor context; historical wooded-cover evidence; neighbouring project-specific critical-habitat/removal evidence; present-day observer occurrence/context evidence including an observer-confirmed Opossum Creek FrogID recording point"
  "exact Springview/project/cadastral/clearing polygon x habitat-function x viable-population/community essentiality; authoritative same-parcel ecology sufficient for the Queensland consumer; validated species occurrence where relied upon"
  "EPBC/proponent 'critical habitat' is not Queensland s 13 classification; neighbouring-project habitat scores do not transfer to Springview; observer-selected FrogID taxon is not expert validation; image-backed neighbourhood is not exact GIS intersection"
  "threatened-species occurrence, corridor membership, old wooded cover or neighbouring-project habitat scores do not individually factor to s 13 essentiality"
  "perform the exact Springview polygon x primary ecology x corridor/habitat-layer join and turn the now-strong landscape-function evidence into a same-parcel s 13 essentiality receipt"

qldS102Priority : LegalPriorityCoordinate
qldS102Priority = legal-priority-coordinate
  interimRestraint
  consumerPaymentOpen
  "Nature Conservation Act ss 102-107 interim conservation-order consumer"
  "source-paid mechanism; 9281/2024/OW identified as approved operational works expressly covering earthworks, vegetation clearing and stormwater; 9293/2024/OW separately covers road work, drainage, stormwater and earthworks; same-landscape habitat/corridor evidence materially strengthened"
  "approved 9281/2024/OW vegetation-clearing drawing/polygon; current commencement/threat chronology; exact affected protected wildlife/habitat; likely significant detrimental effect; exact decision/works conditions relevant to timing"
  "approved clearing entitlement is not proof clearing has commenced; development pressure, local approval or habitat value alone is not an s 102 trigger"
  "project/approval status alone does not determine likely significant detrimental effect or whether the statutory interim-order conditions are met"
  "treat s 102 as a live concurrent lane: acquire the 9281 clearing plans and works chronology now, intersect them with the strongest same-parcel habitat/species evidence, and prepare the interim-order package before irreversible works"

qldS49Priority : LegalPriorityCoordinate
qldS49Priority = legal-priority-coordinate
  permanentProtection
  consumerPaymentOpen
  "Nature Conservation Act s 49 compulsory nature-refuge route"
  "source-paid statutory mechanism; stronger corridor/landscape/ecological corpus now available as supporting material"
  "paid s 13 critical-habitat or area-of-major-interest basis; exact parcels/tenure; refuge suitability; existing-protection position; executive initiation record"
  "qualifying ecology is not executive declaration and does not compel selection of the nature-refuge mechanism"
  "ecological value, corridor importance and s 13 evidence alone do not determine completion of the executive declaration route"
  "prepare parcel/tenure/suitability material in parallel and activate the permanent-protection request immediately once the qualifying s 13 basis is sufficiently paid"

exemptionAuditPriority : LegalPriorityCoordinate
exemptionAuditPriority = legal-priority-coordinate
  exemptionAudit
  consumerPaymentOpen
  "exact Queensland planning/koala exemption or grandfathering applicable to Springview and related components"
  "Council material records mapped koala habitat together with approved/exempted development outcome; the local approval chain is now identified through 6243/2023/LAP, 4272/2020/ADP, 5547/2020/ADP, 7477/2022/ADP, 9281/2024/OW and 9293/2024/OW"
  "exact exemption/grandfathering instrument; temporal and parcel scope; approval-history basis; variation/component coverage; whether later ADPs and operational works remain inside the relied-upon exemption"
  "mapped koala habitat is not a prohibition where a valid exemption applies; no-public-notification status does not establish low development risk or exemption validity"
  "mapped habitat, DA approval, no-notification pathway and project history cannot determine current exemption coverage without the exact instrument and temporal/parcel join"
  "recover the exact exemption authority and test every current ADP/operational-works component and variation against it in parallel with the federal/state ecology lanes"

enforcementPriority : LegalPriorityCoordinate
enforcementPriority = legal-priority-coordinate
  enforcementBackstop
  conditionalBackstop
  "EPBC s 475 / NCA s 173D restraint or enforcement consumer"
  "source-paid enforcement mechanisms; concrete local approval/works objects and federal pending-decision state are now available for conduct monitoring"
  "exact threatened/actual conduct; approval/permit/condition status; contravention/offence or other restraint basis; standing/procedure; chronology"
  "environmental harm, approval existence, clearing entitlement or beneficiary position is not automatically a statutory contravention/offence"
  "harm evidence and project status do not factor to injunction/enforcement availability without the exact breached or threatened legal obligation"
  "keep dormant unless works are threatened or commence; then map the exact conduct to an exact statutory prohibition, condition, offence or restraint basis before invoking enforcement"

------------------------------------------------------------------------
-- Priority policy.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- No-promotion firewalls.
------------------------------------------------------------------------

data AdvocacyInterestCreatesLegalElement : Set where
data PoliticalAlignmentCreatesStatutoryPayment : Set where
data CelebrityAttentionCreatesPreservationOutcome : Set where

advocacyInterestDoesNotCreateLegalElement : AdvocacyInterestCreatesLegalElement → ⊥
advocacyInterestDoesNotCreateLegalElement ()

politicalAlignmentDoesNotCreateStatutoryPayment :
  PoliticalAlignmentCreatesStatutoryPayment → ⊥
politicalAlignmentDoesNotCreateStatutoryPayment ()

celebrityAttentionDoesNotCreatePreservationOutcome :
  CelebrityAttentionCreatesPreservationOutcome → ⊥
celebrityAttentionDoesNotCreatePreservationOutcome ()
