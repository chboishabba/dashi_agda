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

federal8575Priority : LegalPriorityCoordinate
federal8575Priority = legal-priority-coordinate
  immediateFederalDecision
  consumerPaymentOpen
  "EPBC 2019/8575 Part 9 approval/refusal decision due 1 October 2026"
  "controlled-action identity; controlling species/community; authorised delegate; s 130(1A) extension/deadline; January 2026 Preliminary Documentation baseline"
  "Final PD parcel x habitat x impacted/retained hectares x significance x avoidance x residual impact x offsets x conservation-advice/recovery-plan correspondence"
  "controlled action is not refusal; threatened-species presence is not final significant-impact conclusion"
  "species list alone does not determine the approval/refusal answer"
  "recover/extract the Final PD bundle and compile the refusal matrix against the actual statutory consumer"

cumulative8575Priority : LegalPriorityCoordinate
cumulative8575Priority = legal-priority-coordinate
  cumulativeImpactSufficiency
  consumerPaymentOpen
  "EPBC 2019/8575 Preliminary Documentation Request Item 4.6(c) local/regional cumulative-impact response sufficiency"
  "January 2026 PD quotes Item 4.6(c); Plan A7 identifies surrounding EPBC projects; the PD itself describes cumulative and sequential fragmentation"
  "same-object local/regional integration of surrounding development patterns, habitat loss/retention, corridor function and the action's marginal cumulative contribution; Final PD/comment-response and Department sufficiency record"
  "a surrounding-project map is not the requested cumulative analysis; an apparent January response gap is not legal invalidity"
  "project identifiers, generic fragmentation statements, or secondary commentary do not factor to payment of Item 4.6(c)"
  "acquire the Final PD/comment-response first; then snowball primary Scenic/Peninsula/adjacent project geometry and build the time-indexed cumulative habitat/connectivity ledger only where the final material leaves the residual open"

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
  "EPBC s 475 / NCA s 173D restraint or enforcement consumer"
  "source-paid enforcement mechanisms"
  "exact threatened conduct, contravention/offence, approval/permit status, standing/procedure and chronology"
  "environmental harm is not automatically a statutory contravention or nominated offence"
  "harm evidence alone does not factor to injunction/enforcement availability"
  "keep dormant until conduct can be mapped to an exact breached or threatened legal obligation"

------------------------------------------------------------------------
-- Priority policy.
------------------------------------------------------------------------

record LegalOnlyPriorityPolicy : Set where
  constructor legal-only-priority-policy
  field
    federalDecisionFirst : Bool
    cumulativeSufficiencyInsideFederalLane : Bool
    qldS13Second : Bool
    qldS102Third : Bool
    qldS49Fourth : Bool
    exemptionAuditParallel : Bool
    enforcementConditional : Bool
    ashBartyOnCriticalPath : Bool
    politicalPartyAlignmentPaysLegalElement : Bool

canonicalLegalOnlyPriorityPolicy : LegalOnlyPriorityPolicy
canonicalLegalOnlyPriorityPolicy = legal-only-priority-policy
  true true true true true true true false false

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
