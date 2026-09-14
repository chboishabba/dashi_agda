module DASHI.Law.SensibLawWoogaroo9281Condition6aResponseClassifierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogaroo9281Condition6aEvidenceStateExact as Evidence
import DASHI.Law.SensibLawWoogaroo9281EPBCInstrumentDisambiguationExact as Instrument
import DASHI.Law.SensibLawWoogaroo9281BlockingPaymentRouterExact as Router

------------------------------------------------------------------------
-- CONDITION 6(a) RESPONSE CLASSIFIER
--
-- This owner is an intake router for the literal Council-held Condition 6(a)
-- material when acquired.  It does not guess which branch exists today.
-- It preserves the negotiated condition's two genuine branches while keeping
-- unrelated / historical instruments and non-acquisition separate.
--
-- Snowball rule: classification may occur as soon as a manifestation is
-- acquired, but satisfaction / federal-authorisation promotion cannot skip
-- primary source identity, same proposed clearing/action, geometry, clearing
-- phase, operative time, or Council's actual treatment of the submission.
------------------------------------------------------------------------

data Condition6aResponseKind : Set where
  dcceewNoControlledActionEvidence : Condition6aResponseKind
  commonwealthPart9Approval : Condition6aResponseKind
  historicalOrUnrelatedInstrument : Condition6aResponseKind
  condition6aRecordUnavailable : Condition6aResponseKind

data ResponseAcquisitionState : Set where
  responseNotAcquired : ResponseAcquisitionState
  responsePrimaryAcquired : ResponseAcquisitionState
  responseSecondaryLocatorOnly : ResponseAcquisitionState

record Condition6aResponseCase : Set where
  constructor condition6a-response-case
  field
    kind : Condition6aResponseKind
    acquisitionState : ResponseAcquisitionState
    boundedMeaning : String
    primaryManifestationRequired : Bool
    sameProposedClearingRequired : Bool
    sameActionRequired : Bool
    authoritativeGeometryRequired : Bool
    sameClearingPhaseRequired : Bool
    operativeAtRelevantTimeRequired : Bool
    councilAcceptanceRequired : Bool
    classificationPaysConditionSatisfaction : Bool
    classificationPaysFederalAuthorisation : Bool

open Condition6aResponseCase public

noControlledActionEvidenceCase : Condition6aResponseCase
noControlledActionEvidenceCase = condition6a-response-case
  dcceewNoControlledActionEvidence
  responseNotAcquired
  "Condition 6(a) branch A: primary DCCEEW evidence stating that the proposed clearing works do not constitute a controlled action. The evidence must be bound to the same proposed clearing; generic or different-action correspondence cannot be transferred."
  true true true true true true true false false

part9ApprovalCase : Condition6aResponseCase
part9ApprovalCase = condition6a-response-case
  commonwealthPart9Approval
  responseNotAcquired
  "Condition 6(a) branch B: a literal Commonwealth approval supplied for the proposed clearing works. The approval must be identified and reconciled to the same action, geometry, clearing phase and operative time before it can be treated as relevant payment."
  true true true true true true true false false

historicalOrUnrelatedInstrumentCase : Condition6aResponseCase
historicalOrUnrelatedInstrumentCase = condition6a-response-case
  historicalOrUnrelatedInstrument
  responseNotAcquired
  "A historical or different-action EPBC instrument may be a real operative approval but cannot discharge Condition 6(a) for 9281 merely because it concerns Springfield, nearby land or the same corporate ecosystem."
  true true true true true true true false false

condition6aRecordUnavailableCase : Condition6aResponseCase
condition6aRecordUnavailableCase = condition6a-response-case
  condition6aRecordUnavailable
  responseNotAcquired
  "No literal Condition 6(a) satisfaction record has yet been acquired by DASHI. This is an acquisition state only: it neither proves non-submission nor proves satisfaction."
  true true true true true true true false false

------------------------------------------------------------------------
-- Current classification state.
------------------------------------------------------------------------

currentCondition6aClassificationState : Condition6aResponseCase
currentCondition6aClassificationState = condition6aRecordUnavailableCase

condition6aResponseTemplates : List Condition6aResponseCase
condition6aResponseTemplates =
  noControlledActionEvidenceCase ∷
  part9ApprovalCase ∷
  historicalOrUnrelatedInstrumentCase ∷
  condition6aRecordUnavailableCase ∷
  []

------------------------------------------------------------------------
-- WrongType / no-skip firewalls.
------------------------------------------------------------------------

data NoControlledActionEvidenceSkipsSameProposedClearing : Set where
data Part9ApprovalSkipsActionGeometryPhaseAndTime : Set where
data HistoricalInstrumentTransfersAuthorisation : Set where
data ClassificationEqualsConditionSatisfaction : Set where
data RecordUnavailableProvesNonSubmission : Set where

noControlledActionEvidenceNeedsSameProposedClearing :
  NoControlledActionEvidenceSkipsSameProposedClearing → ⊥
noControlledActionEvidenceNeedsSameProposedClearing ()

part9ApprovalNeedsSameActionGeometryPhaseAndOperativeTime :
  Part9ApprovalSkipsActionGeometryPhaseAndTime → ⊥
part9ApprovalNeedsSameActionGeometryPhaseAndOperativeTime ()

historicalInstrumentDoesNotTransferAuthorisation :
  HistoricalInstrumentTransfersAuthorisation → ⊥
historicalInstrumentDoesNotTransferAuthorisation ()

classificationDoesNotEqualConditionSatisfaction :
  ClassificationEqualsConditionSatisfaction → ⊥
classificationDoesNotEqualConditionSatisfaction ()

recordUnavailableDoesNotProveNonSubmission :
  RecordUnavailableProvesNonSubmission → ⊥
recordUnavailableDoesNotProveNonSubmission ()

------------------------------------------------------------------------
-- Reuse-only receipts.  No source authority is re-minted here.
------------------------------------------------------------------------

literalCondition6aEvidenceObject : Evidence.Condition6aEvidenceObject
literalCondition6aEvidenceObject = Evidence.condition6aLiteralSubmission

literalCondition6aInstrumentCandidate : Instrument.InstrumentCandidate
literalCondition6aInstrumentCandidate = Instrument.condition6aLiteralInstrumentStillOpen

blockingPaymentReceipt : Router.BlockingPayment
blockingPaymentReceipt = Router.condition6aLiteralSubmissionPayment

record Condition6aResponsePareto : Set where
  constructor condition6a-response-pareto
  field
    acquireLiteralRecordFirst : Bool
    distinguishNoControlledActionFromApprovalBranch : Bool
    classifyHistoricalInstrumentSeparately : Bool
    sameProposedClearingBeforeNoControlledActionPromotion : Bool
    sameActionGeometryPhaseTimeBeforeApprovalPromotion : Bool
    councilAcceptanceBeforeConditionSatisfaction : Bool
    unavailableRecordCanProveNonSubmission : Bool
    classificationCanPayFederalAuthorisation : Bool
    secondaryMayLocatePrimary : Bool
    secondaryMayPayPrimary : Bool

canonicalCondition6aResponsePareto : Condition6aResponsePareto
canonicalCondition6aResponsePareto = condition6a-response-pareto
  true true true true true true false false true false
