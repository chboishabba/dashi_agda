module DASHI.Law.SensibLawWoogarooLegalPriorityRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooPreservationRoadmapExact as Roadmap
import DASHI.Law.SensibLawWoogarooEPBC8575DecisionConsumerMatrixExact as EPBC
import DASHI.Law.SensibLawWoogarooEPBC8575PortalClockManifestationExact as Clock
import DASHI.Law.SensibLawWoogarooAdmissibleFactorsWrongTypeAtomBridgeExact as AFW

data LegalPriority : Set where
  localExecutionGate : LegalPriority
  immediateFederalDecision : LegalPriority
  cumulativeImpactSufficiency : LegalPriority
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

condition6aPriority : LegalPriorityCoordinate
condition6aPriority = legal-priority-coordinate
  localExecutionGate
  consumerPaymentOpen
  "9281/2024/OW Condition 6(a) -> Planning Act 2016 s 72 commencement gate, with ss 164 and 180 available for counsel review if the factual/legal trigger is paid"
  "Condition 6(a) requirement is source-paid; local negotiated approval is source-paid; post-decision satisfaction, Council treatment, same-clearing-phase prestart package and commencement remain open"
  "literal Condition 6(a) satisfaction submission; Council acceptance/assessment; signed same-phase environmental preclearance; authoritative geometry; imminence"
  "an unlocated compliance record is not non-compliance; an unsatisfied-condition hypothesis is not a development offence; s 180 availability is not an order"
  "public-register silence, generic EPBC notes and historical Springfield approvals do not factor to Condition 6(a) satisfaction"
  "acquire the post-decision Condition 6(a) satisfaction/acceptance record and same-phase prestart package before widening the execution theory"

federal8575Priority : LegalPriorityCoordinate
federal8575Priority = legal-priority-coordinate
  immediateFederalDecision
  consumerPaymentOpen
  "EPBC 2019/8575 Part 9 decision: 15 October 2026 public Commonwealth notice says APPROVED WITH CONDITIONS; operative signed approval, authorisation and full conditions still to acquire"
  "official public notice is a dated decision-status receipt; section 95B(2) 23 July 2026 notice recorded 1786 comments; January preliminary documentation and surrounding project map remain separate source objects"
  "signed approval and delegate identity; statement of reasons and section 135A recommendation report; final PD and complete comment-response; current legal framework/transitional provisions; pre-clearance conditions, offsets and review standing/deadline"
  "approval status is not the signed decision; dated public comment count is not the decision-maker's complete evidentiary consideration; Minister's portfolio responsibility does not by itself prove Minister personally signed"
  "housing delivery rhetoric, indexed political interests, a 2025 Queensland ministerial lobbying meeting or a 2004 gas alliance do not factor to EPBC decision legality or a conflict finding"
  "urgent counsel filing/standing/possible interim orders assessment; obtain original signed notice and section 135A recommendation report; freeze public decision and ecological evidence with dates and hashes; calculate exact ADJR or other Federal Court deadlines without assuming public notice starts one universal 28-day clock"

-- The pre-decision s130 clock witnesses remain historically valid source receipts,
-- but their 1 October extension must NOT be interpreted as a live future deadline.
-- The separate post-approval source owner supplies current approval evidence.

federalClockReceipt : Clock.ClockReceipt
federalClockReceipt = Clock.section130FortyBusinessDayClock

ministerReceiptResidual : Clock.ClockReceipt
ministerReceiptResidual = Clock.minister95BReceiptDateOpen

cumulative8575Priority : LegalPriorityCoordinate
cumulative8575Priority = legal-priority-coordinate
  cumulativeImpactSufficiency
  consumerPaymentOpen
  "EPBC 2019/8575 Preliminary Documentation Request Item 4.6(c) local/regional cumulative-impact response sufficiency"
  "January 2026 PD quotes Item 4.6(c); Plan A7 identifies surrounding EPBC projects; the PD itself describes cumulative and sequential fragmentation"
  "same-object local/regional integration of surrounding development patterns, habitat loss/retention, corridor function and the action's marginal cumulative contribution; Final PD/comment-response and Department sufficiency record"
  "a surrounding-project map is not the requested cumulative analysis; an apparent January response gap is not legal invalidity"
  "project identifiers, generic fragmentation statements, or secondary commentary do not factor to payment of Item 4.6(c)"
  "post-approval: urgently compare final-PD/comment-response, recommendation report, signed 15 October decision and conditions; reconcile Item 4.6(c) with actual local/regional functional connectivity analysis, then commission same-parcel specialist review for counsel"

qldS13Priority : LegalPriorityCoordinate
qldS13Priority = legal-priority-coordinate
  sameParcelCriticalHabitat
  consumerPaymentOpen
  "Nature Conservation Act 1992 (Qld) s 13 critical-habitat application to exact threatened Woogaroo parcels"
  "s 13 legal definition; threatened-species/habitat evidence; corridor/fragmentation evidence at broader fibres"
  "same-parcel habitat-function evidence showing essentiality to conservation of a viable protected-wildlife population or native-wildlife community"
  "EPBC/proponent 'critical habitat' terminology is not the Queensland s 13 legal classification"
  "threatened-species occurrence does not factor to s 13 essentiality"
  "join exact project/cadastral footprint to primary ecology maps/tables and Queensland habitat layers, then build the s 13 application receipt"

qldS102Priority : LegalPriorityCoordinate
qldS102Priority = legal-priority-coordinate
  interimRestraint
  consumerPaymentOpen
  "Nature Conservation Act ss 102-107 interim conservation-order consumer"
  "source-paid statutory mechanism; live development/clearing pressure"
  "exact threatening process, timing, affected wildlife/habitat, and likely significant detrimental effect"
  "delay or development pressure is not itself an s 102 trigger"
  "project status alone does not determine whether the threatening-process statutory conditions are satisfied"
  "build a dated works/threat chronology and bind it to the strongest same-parcel habitat evidence before physical works commence"

qldS49Priority : LegalPriorityCoordinate
qldS49Priority = legal-priority-coordinate
  permanentProtection
  consumerPaymentOpen
  "Nature Conservation Act s 49 compulsory nature-refuge route"
  "source-paid statutory mechanism"
  "s 13 critical-habitat or area-of-major-interest basis; exact parcels/tenure; refuge suitability; executive initiation record"
  "qualifying ecological evidence is not the executive declaration itself"
  "ecological value alone does not determine whether the statutory/executive declaration route is completed"
  "compile the permanent-protection request in parallel once the s 13 same-parcel evidence is paid"

exemptionAuditPriority : LegalPriorityCoordinate
exemptionAuditPriority = legal-priority-coordinate
  exemptionAudit
  consumerPaymentOpen
  "exact Queensland planning/koala exemption or grandfathering applicable to Springview and related components"
  "Council material records mapped koala habitat together with approved/exempted development outcome"
  "exact instrument, temporal scope, parcel scope, approval history, and variation/component coverage"
  "mapped koala habitat is not equivalent to a prohibition where an exemption applies"
  "mapped habitat cannot determine the approval outcome without exemption/history coordinates"
  "recover the exact exemption authority and test whether every current component/variation remains inside it"

enforcementPriority : LegalPriorityCoordinate
enforcementPriority = legal-priority-coordinate
  enforcementBackstop
  conditionalBackstop
  "parallel Queensland Planning Act s 180 / EPBC s 475 / NCA enforcement or restraint consumers"
  "source-paid statutory mechanisms including the 9281 Condition 6(a) -> Planning Act ss 72/164/180 sequence and the federal s 67A -> s 475 route"
  "exact threatened conduct, condition/contravention status, same-action/phase/geometry, standing/procedure and chronology"
  "environmental harm, public silence or local approval is not automatically a statutory contravention or offence"
  "harm evidence alone does not factor to injunction/enforcement availability"
  "keep fail-closed until proposed conduct can be mapped to an exact breached or threatened legal obligation and counsel validates the procedural vehicle"

record LegalOnlyPriorityPolicy : Set where
  constructor legal-only-priority-policy
  field
    localExecutionGateFirst : Bool
    federalDecisionParallelSecond : Bool
    cumulativeSufficiencyInsideFederalLane : Bool
    qldS102HighAlphaParallel : Bool
    qldS13HighAlphaParallel : Bool
    qldS49SlowerBackstop : Bool
    exemptionAuditParallel : Bool
    enforcementConditional : Bool
    ashBartyOnCriticalPath : Bool
    politicalPartyAlignmentPaysLegalElement : Bool

canonicalLegalOnlyPriorityPolicy : LegalOnlyPriorityPolicy
canonicalLegalOnlyPriorityPolicy = legal-only-priority-policy
  true true true true true true true true false false

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
