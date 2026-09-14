module DASHI.Law.SensibLawWoogaroo9281Condition6aEvidenceStateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Law.SensibLawWoogaroo9281PreclearanceConvergenceExact as Preclear
import DASHI.Law.SensibLawWoogaroo9281EPBCInstrumentDisambiguationExact as Instrument

------------------------------------------------------------------------
-- 9281 CONDITION 6(a): EVIDENCE STATE, NOT ABSENCE-INFERENCE
--
-- Highest-alpha preservation question:
--   what literal record was accepted by Ipswich to satisfy negotiated
--   condition 6(a), and which clearing phase / Commonwealth action does it
--   actually cover?
--
-- Public non-location is not a proof that the record was never submitted.
-- This module therefore treats public-register visibility, Council custody,
-- instrument identity, same-action identity and same-clearing-phase identity
-- as separate coordinates.
------------------------------------------------------------------------

data CouncilCustodyWorld : Set where
  submittedButNotPubliclyLocated : CouncilCustodyWorld
  notYetSubmitted : CouncilCustodyWorld

data PublicRegisterSurface : Set where
  noCondition6aSatisfactionRecordLocated : PublicRegisterSurface

data Condition6aSatisfactionStatus : Set where
  satisfactionSubmitted : Condition6aSatisfactionStatus
  satisfactionNotSubmitted : Condition6aSatisfactionStatus

publicRegisterObserver : CouncilCustodyWorld → PublicRegisterSurface
publicRegisterObserver submittedButNotPubliclyLocated = noCondition6aSatisfactionRecordLocated
publicRegisterObserver notYetSubmitted = noCondition6aSatisfactionRecordLocated

condition6aSatisfactionQuery : CouncilCustodyWorld → Condition6aSatisfactionStatus
condition6aSatisfactionQuery submittedButNotPubliclyLocated = satisfactionSubmitted
condition6aSatisfactionQuery notYetSubmitted = satisfactionNotSubmitted

condition6aSatisfactionDiffers :
  condition6aSatisfactionQuery submittedButNotPubliclyLocated ≡
  condition6aSatisfactionQuery notYetSubmitted → ⊥
condition6aSatisfactionDiffers ()

condition6aSatisfactionNotRecoverableFromPublicRegister :
  INF.FactorsThrough publicRegisterObserver condition6aSatisfactionQuery → ⊥
condition6aSatisfactionNotRecoverableFromPublicRegister =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      submittedButNotPubliclyLocated
      notYetSubmitted
      refl
      condition6aSatisfactionDiffers)

------------------------------------------------------------------------
-- WrongType / no-skip firewalls.
------------------------------------------------------------------------

data PublicSilenceProvesNonSubmission : Set where
data ConditionExistenceProvesSatisfaction : Set where
data FinalPDNoticeProvesNoLaterPart9Decision : Set where
data LocatedApprovalProvesSameClearingPhase : Set where
data SameProjectNumberProvesSameGeometry : Set where

publicSilenceDoesNotProveNonSubmission : PublicSilenceProvesNonSubmission → ⊥
publicSilenceDoesNotProveNonSubmission ()

conditionExistenceDoesNotProveSatisfaction : ConditionExistenceProvesSatisfaction → ⊥
conditionExistenceDoesNotProveSatisfaction ()

finalPDNoticeDoesNotProveNoLaterPart9Decision : FinalPDNoticeProvesNoLaterPart9Decision → ⊥
finalPDNoticeDoesNotProveNoLaterPart9Decision ()

locatedApprovalDoesNotProveSameClearingPhase : LocatedApprovalProvesSameClearingPhase → ⊥
locatedApprovalDoesNotProveSameClearingPhase ()

sameProjectNumberDoesNotProveSameGeometry : SameProjectNumberProvesSameGeometry → ⊥
sameProjectNumberDoesNotProveSameGeometry ()

------------------------------------------------------------------------
-- The evidence state carried for each acquired object.
------------------------------------------------------------------------

data EvidenceAcquisitionState : Set where
  notAcquired : EvidenceAcquisitionState
  acquiredPrimary : EvidenceAcquisitionState
  acquiredSecondaryLocatorOnly : EvidenceAcquisitionState

data EvidenceRole : Set where
  condition6aSubmissionRole : EvidenceRole
  councilAcceptanceRole : EvidenceRole
  prestartRecordRole : EvidenceRole
  environmentalPreclearanceRole : EvidenceRole
  faunaPreclearanceRole : EvidenceRole
  arboristPrestartRole : EvidenceRole
  accessWorksLicenceRole : EvidenceRole

record Condition6aEvidenceObject : Set where
  constructor condition6a-evidence-object
  field
    role : EvidenceRole
    exactObject : String
    state : EvidenceAcquisitionState
    primaryRequiredForPromotion : Bool
    mayPayInstrumentIdentity : Bool
    mayPaySameClearingPhase : Bool
    mayPayImminence : Bool
    mayPayFederalAuthorisation : Bool

open Condition6aEvidenceObject public

condition6aLiteralSubmission : Condition6aEvidenceObject
condition6aLiteralSubmission = condition6a-evidence-object
  condition6aSubmissionRole
  "The literal 9281/2024/OW negotiated condition 6(a) submission: DCCEEW no-controlled-action evidence or the Commonwealth approval supplied for the proposed clearing works."
  notAcquired true true true true false

condition6aCouncilAcceptance : Condition6aEvidenceObject
condition6aCouncilAcceptance = condition6a-evidence-object
  councilAcceptanceRole
  "Council receipt, assessment note, acceptance record or correspondence showing how condition 6(a) was treated before the prestart meeting."
  notAcquired true true true true false

prestartMeetingRecord : Condition6aEvidenceObject
prestartMeetingRecord = condition6a-evidence-object
  prestartRecordRole
  "Pre-start notice, agenda, minutes, attendance record and date for the relevant 9281 clearing phase."
  notAcquired true false true true false

signedEnvironmentalPreclearancePackage : Condition6aEvidenceObject
signedEnvironmentalPreclearancePackage = condition6a-evidence-object
  environmentalPreclearanceRole
  "Stage-specific Environmental Pre-Clearance Checklist and Package, including approval documents or references, signatures, phase identity and Environmental Coordinator sign-off."
  notAcquired true true true true false

faunaPreclearanceRecord : Condition6aEvidenceObject
faunaPreclearanceRecord = condition6a-evidence-object
  faunaPreclearanceRole
  "Condition 9 spotter-catcher identity/licence and Pre-Clearance Fauna Management Plan for the same clearing phase."
  notAcquired true false true true false

arboristPrestartRecord : Condition6aEvidenceObject
arboristPrestartRecord = condition6a-evidence-object
  arboristPrestartRole
  "Condition 8 Arboricultural Impact Assessment and associated pre-start approval for clearing within ten metres of open-space areas."
  notAcquired true false true true false

accessWorksLicenceRecord : Condition6aEvidenceObject
accessWorksLicenceRecord = condition6a-evidence-object
  accessWorksLicenceRole
  "Access and Works Licence Agreement for any works in Council-controlled land."
  notAcquired true false true true false

condition6aAcquisitionBundle : List Condition6aEvidenceObject
condition6aAcquisitionBundle =
  condition6aLiteralSubmission ∷
  condition6aCouncilAcceptance ∷
  signedEnvironmentalPreclearancePackage ∷
  prestartMeetingRecord ∷
  faunaPreclearanceRecord ∷
  arboristPrestartRecord ∷
  accessWorksLicenceRecord ∷
  []

------------------------------------------------------------------------
-- Promotion ladder.  Same-phase identity is deliberately explicit because a
-- valid approval or checklist for another Springfield stage cannot pay the
-- 9281 clearing phase presently at issue.
------------------------------------------------------------------------

record Condition6aPromotionGate : Set where
  constructor condition6a-promotion-gate
  field
    primaryManifestationAcquired : Bool
    literalInstrumentIdentified : Bool
    sameActionPaid : Bool
    sameGeometryPaid : Bool
    sameClearingPhasePaid : Bool
    operativeAtRelevantTimePaid : Bool
    mayPromoteToFederalAuthorisationConclusion : Bool

open Condition6aPromotionGate public

sameClearingPhaseRequiredBeforePromotion : Condition6aPromotionGate
sameClearingPhaseRequiredBeforePromotion = condition6a-promotion-gate
  false false false false false false false

record Condition6aEvidencePareto : Set where
  constructor condition6a-evidence-pareto
  field
    literalSubmissionFirst : Bool
    councilAcceptanceSecond : Bool
    signedPackageCanJoinInstrumentAndImminence : Bool
    publicRegisterSilenceCanProveNonSubmission : Bool
    finalPDNoticeCanProveNoLaterDecision : Bool
    sameProjectNumberCanSkipGeometry : Bool
    sameClearingPhaseRequired : Bool
    secondaryMayLocatePrimary : Bool
    secondaryMayPayPrimary : Bool

canonicalCondition6aEvidencePareto : Condition6aEvidencePareto
canonicalCondition6aEvidencePareto = condition6a-evidence-pareto
  true true true false false false true true false

------------------------------------------------------------------------
-- Reuse receipts: this owner does not re-mint source authority.
------------------------------------------------------------------------

localConditionReceipt = Preclear.condition6aLocalFederalGate
signedPackageProtocolReceipt = Preclear.springfield8575SignedChecklistProtocol
literalInstrumentCandidate = Instrument.condition6aLiteralInstrumentStillOpen
