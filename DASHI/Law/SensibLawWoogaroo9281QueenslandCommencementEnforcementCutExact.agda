module DASHI.Law.SensibLawWoogaroo9281QueenslandCommencementEnforcementCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawWoogaroo9281PreclearanceConvergenceExact as Preclear
import DASHI.Law.SensibLawWoogaroo9281Condition6aEvidenceStateExact as Evidence

------------------------------------------------------------------------
-- 9281 QUEENSLAND COMMENCEMENT / ENFORCEMENT CUT
--
-- This owner records a distinct State-law preservation route.  It does not
-- re-characterise the Commonwealth merits or infer a development offence from
-- public silence.  Its purpose is to preserve the literal statutory sequence:
--
--   condition 6(a) pre-start requirement
--     -> Planning Act 2016 s 72 commencement gate
--     -> s 164 development-approval compliance offence
--     -> s 180 enforcement / interim enforcement route.
--
-- Whether the facts satisfy that sequence remains an evidence + counsel issue.
------------------------------------------------------------------------

planningAct2016CurrentSource : Source.AttributedSource
planningAct2016CurrentSource = Source.mkNoDOISource
  "Queensland Parliamentary Counsel"
  "Planning Act 2016"
  "Queensland legislation"
  "current as at 3 September 2026"
  "https://www.legislation.qld.gov.au/view/html/inforce/current/act-2016-025"
  Source.governmentSource
  "Primary legislation source for sections 72, 164 and 180. Citation records the statutory text but does not determine application to the 9281 facts."
  Source.publicAttribution

data QldSection : Set where
  section72 : QldSection
  section164 : QldSection
  section180 : QldSection

record StatutoryReceipt : Set where
  constructor statutory-receipt
  field
    section : QldSection
    source : Source.AttributedSource
    exactRule : String
    primaryTextPaid : Bool
    factsApplied : Bool
    offenceEstablished : Bool

open StatutoryReceipt public

section72CommencementGate : StatutoryReceipt
section72CommencementGate = statutory-receipt
  section72
  planningAct2016CurrentSource
  "Development under a development approval may start when all development permits have effect and all development conditions required to be complied with before development starts have been complied with."
  true false false

section164ApprovalComplianceOffence : StatutoryReceipt
section164ApprovalComplianceOffence = statutory-receipt
  section164
  planningAct2016CurrentSource
  "A person must not contravene a development approval."
  true false false

section180AnyPersonEnforcementRoute : StatutoryReceipt
section180AnyPersonEnforcementRoute = statutory-receipt
  section180
  planningAct2016CurrentSource
  "Any person may start P&E Court proceedings for an enforcement order."
  true false false

section180FutureOffenceInterimRoute : StatutoryReceipt
section180FutureOffenceInterimRoute = statutory-receipt
  section180
  planningAct2016CurrentSource
  "The P&E Court may act where a development offence has been or will be committed unless an order is made, may make an interim enforcement order, and may direct a respondent not to start an activity constituting the offence."
  true false false

------------------------------------------------------------------------
-- Weld to the already-paid local condition without re-minting its authority.
------------------------------------------------------------------------

condition6aReceipt : Preclear.PreclearanceReceipt
condition6aReceipt = Preclear.condition6aLocalFederalGate

condition6aEvidenceObject : Evidence.Condition6aEvidenceObject
condition6aEvidenceObject = Evidence.condition6aLiteralSubmission

record CommencementGateWeld : Set where
  constructor commencement-gate-weld
  field
    condition6aRequiresPaymentBeforePrestart : Bool
    section72RequiresPreStartConditionsPaid : Bool
    literalCondition6aSatisfactionAcquired : Bool
    sameClearingPhasePaid : Bool
    mayConcludeDevelopmentMayStart : Bool

open CommencementGateWeld public

condition6aFeedsSection72Gate : CommencementGateWeld
condition6aFeedsSection72Gate = commencement-gate-weld
  true true false false false

------------------------------------------------------------------------
-- WrongType / no-promotion firewalls.
------------------------------------------------------------------------

data Unsatisfied6aAloneProvesDevelopmentOffence : Set where
data PublicSilencePaysSection72NonCompliance : Set where
data QldCutReplacesFederalCut : Set where
data Section180AvailabilityProvesOrderWillIssue : Set where
data LocalApprovalProvesCommencement : Set where

condition6aUnsatisfiedDoesNotByItselfProveDevelopmentOffence :
  Unsatisfied6aAloneProvesDevelopmentOffence → ⊥
condition6aUnsatisfiedDoesNotByItselfProveDevelopmentOffence ()

publicRegisterSilenceDoesNotPaySection72NonCompliance :
  PublicSilencePaysSection72NonCompliance → ⊥
publicRegisterSilenceDoesNotPaySection72NonCompliance ()

qldCutDoesNotReplaceFederalCut : QldCutReplacesFederalCut → ⊥
qldCutDoesNotReplaceFederalCut ()

section180AvailabilityDoesNotProveOrderWillIssue :
  Section180AvailabilityProvesOrderWillIssue → ⊥
section180AvailabilityDoesNotProveOrderWillIssue ()

localApprovalDoesNotProveCommencement : LocalApprovalProvesCommencement → ⊥
localApprovalDoesNotProveCommencement ()

------------------------------------------------------------------------
-- Fail-closed preservation router.
------------------------------------------------------------------------

record QueenslandPreservationCut : Set where
  constructor queensland-preservation-cut
  field
    condition6aRequirementPaid : Bool
    condition6aSatisfactionPaid : Bool
    prestartOrCommencementPaid : Bool
    samePhasePaid : Bool
    section72ApplicationReviewed : Bool
    section164ContraventionReviewed : Bool
    section180ProcedureReviewed : Bool
    counselReady : Bool

open QueenslandPreservationCut public

canonicalQueenslandPreservationCut : QueenslandPreservationCut
canonicalQueenslandPreservationCut = queensland-preservation-cut
  true false false false false false false false

record QueenslandCutPareto : Set where
  constructor queensland-cut-pareto
  field
    condition6aSatisfactionFirst : Bool
    prestartSamePhaseSecond : Bool
    section72BeforeOffenceConclusion : Bool
    section164BeforeSection180Merits : Bool
    stateAndFederalRoutesRemainParallel : Bool
    publicSilenceCannotCloseEvidenceGap : Bool

canonicalQueenslandCutPareto : QueenslandCutPareto
canonicalQueenslandCutPareto = queensland-cut-pareto
  true true true true true true
