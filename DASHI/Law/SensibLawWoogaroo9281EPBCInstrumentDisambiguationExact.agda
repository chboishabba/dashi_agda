module DASHI.Law.SensibLawWoogaroo9281EPBCInstrumentDisambiguationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawSpringfieldFirstNineApprovalGasEndpointBridgeExact as FirstNine
import DASHI.Law.SensibLawWoogaroo9281FederalPrestartGateExact as Prestart
import DASHI.Law.SensibLawWoogaroo9281SourceDerivedSpatialOverlapExact as P3

firstNine2016ReferralDecision : Source.AttributedSource
firstNine2016ReferralDecision = Source.mkNoDOISource
  "Australian Government Department of the Environment"
  "Referral decision and designated proponent - First Nine master planned residential development, Brookwater, Qld (2016/7676)"
  "EPBC referral decision"
  "2016"
  "EPBC 2016/7676 referral decision record"
  Source.governmentSource
  "Primary Commonwealth decision: First Nine was determined a controlled action under sections 18 and 18A; Springfield Land Corporation Pty Limited, ACN 055714531, was the designated proponent; preliminary documentation was selected as the assessment approach."
  Source.publicAttribution

firstNine2016VariationDecision : Source.AttributedSource
firstNine2016VariationDecision = Source.mkNoDOISource
  "Australian Government Department of the Environment"
  "Variation of proposed action - First Nine master planned residential development (EPBC 2016/7676)"
  "EPBC variation decision"
  "2016"
  "EPBC 2016/7676 variation decision record, decision 2 August 2016"
  Source.governmentSource
  "Primary Commonwealth variation manifestation: the varied First Nine action uses two sites east of Brookwater. The associated request described a 47.25 ha revised referral area comprising the original 40.8 ha footprint plus a 6.45 ha disposal area. This record is an action-boundary coordinate, not a 9281 authorisation receipt."
  Source.publicAttribution

firstNine2016FinalApprovalReceipt : Source.AttributedSource
firstNine2016FinalApprovalReceipt = FirstNine.firstNineFinalApproval

record ExistingFederalInstrument : Set where
  constructor existing-federal-instrument
  field
    projectRef : String
    actionDescription : String
    approvalHolder : String
    operativeApproval : Bool
    approvalExpiry : String
    maxKoalaHabitatClearingCentiHa : Nat
    sameActionAs9281Paid : Bool
    sameActionAs8575Paid : Bool
    mayDischarge9281Condition6aNow : Bool

open ExistingFederalInstrument public

firstNineApprovalIsOperativeButDifferentAction : ExistingFederalInstrument
firstNineApprovalIsOperativeButDifferentAction = existing-federal-instrument
  "EPBC 2016/7676"
  "First Nine master planned residential development east of Brookwater, subject to the varied action accepted 2 August 2016"
  "Springfield Land Corporation Pty Limited"
  true
  "21 December 2038"
  4620
  false
  false
  false

springfield8575FinalPDNotice : Source.AttributedSource
springfield8575FinalPDNotice = Source.mkNoDOISource
  "National Environmental Protection Agency / Australian Government"
  "Springfield Residential Development, Springfield, Queensland (EPBC 2019/8575) - s95B final preliminary documentation notice"
  "EPBC final preliminary documentation notice"
  "2026"
  "EPBC 2019/8575 final preliminary documentation publication notice"
  Source.governmentSource
  "Primary Commonwealth notice: Cherish Enterprises Pty Ltd is seeking approval for the Springfield Residential Development; the action is a controlled action assessed by preliminary documentation. The notice records the closed public-comment process and publication of final preliminary documentation, but is not itself a Part 9 approval instrument."
  Source.publicAttribution

data EPBC2016ApprovalPays9281Condition6aWithoutSameAction : Set where
data EPBC2016ApprovalPays8575Authorisation : Set where
data GenericSpringfieldApprovalIdentifiesCondition6aInstrument : Set where
data FinalPDNoticeEqualsPart9Approval : Set where

epbc2016ApprovalDoesNotPay9281Condition6aWithoutSameAction :
  EPBC2016ApprovalPays9281Condition6aWithoutSameAction → ⊥
epbc2016ApprovalDoesNotPay9281Condition6aWithoutSameAction ()

epbc2016ApprovalDoesNotPay8575Authorisation :
  EPBC2016ApprovalPays8575Authorisation → ⊥
epbc2016ApprovalDoesNotPay8575Authorisation ()

genericSpringfieldApprovalDoesNotIdentifyCondition6aInstrument :
  GenericSpringfieldApprovalIdentifiesCondition6aInstrument → ⊥
genericSpringfieldApprovalDoesNotIdentifyCondition6aInstrument ()

finalPDNoticeDoesNotEqualPart9Approval : FinalPDNoticeEqualsPart9Approval → ⊥
finalPDNoticeDoesNotEqualPart9Approval ()

data InstrumentCandidateStatus : Set where
  primaryInstrumentPaid : InstrumentCandidateStatus
  identityOnly : InstrumentCandidateStatus
  acquisitionOpen : InstrumentCandidateStatus

data FederalInstrumentCoordinate : Set where
  epbc2014_7306 : FederalInstrumentCoordinate
  epbc2016_7676 : FederalInstrumentCoordinate
  epbc2019_8575 : FederalInstrumentCoordinate
  condition6aLiteralSubmission : FederalInstrumentCoordinate

record InstrumentCandidate : Set where
  constructor instrument-candidate
  field
    coordinate : FederalInstrumentCoordinate
    exactRef : String
    boundedRole : String
    status : InstrumentCandidateStatus
    sameAction9281Paid : Bool
    mayBeUsedAsCondition6aPayment : Bool

open InstrumentCandidate public

firstNine2016Candidate : InstrumentCandidate
firstNine2016Candidate = instrument-candidate
  epbc2016_7676
  "EPBC 2016/7676"
  "Operative First Nine approval through 21 December 2038; useful prior-action / cumulative / geometry coordinate, but no same-action weld to 9281 has been paid."
  primaryInstrumentPaid
  false
  false

prior2014Candidate : InstrumentCandidate
prior2014Candidate = instrument-candidate
  epbc2014_7306
  "EPBC 2014/7306"
  "Prior Springfield approval shown as a distinct approval area in the 2019/8575 proponent approval-area mapping; exact instrument and authoritative geometry still require same-object reconciliation for 9281."
  identityOnly
  false
  false

springfield8575Candidate : InstrumentCandidate
springfield8575Candidate = instrument-candidate
  epbc2019_8575
  "EPBC 2019/8575"
  "Current Springfield Residential Development controlled-action assessment. Final-PD publication is paid; a Part 9 approval instrument must be separately located and identified if relied upon for condition 6(a)."
  identityOnly
  false
  false

condition6aLiteralInstrumentStillOpen : InstrumentCandidate
condition6aLiteralInstrumentStillOpen = instrument-candidate
  condition6aLiteralSubmission
  "9281/2024/OW negotiated condition 6(a) satisfaction record"
  "First-paying object: the literal DCCEEW no-controlled-action evidence or Commonwealth approval actually submitted to Ipswich before the prestart meeting, including the project/action reference relied upon."
  acquisitionOpen
  false
  false

condition6aCandidateOrder : List InstrumentCandidate
condition6aCandidateOrder =
  condition6aLiteralInstrumentStillOpen ∷
  prior2014Candidate ∷
  firstNine2016Candidate ∷
  springfield8575Candidate ∷
  []

record InstrumentDisambiguationPareto : Set where
  constructor instrument-disambiguation-pareto
  field
    condition6aLiteralSubmissionFirst : Bool
    existingApprovalExistenceInsufficient : Bool
    sameActionBeforeAuthorisationTransfer : Bool
    separate2014_2016_2019Actions : Bool
    primarySourceBeforePromotion : Bool
    secondaryMayLocatePrimary : Bool
    secondaryMayPayPrimary : Bool
    historicalApprovalMaySkipGeometry : Bool

canonicalInstrumentDisambiguationPareto : InstrumentDisambiguationPareto
canonicalInstrumentDisambiguationPareto = instrument-disambiguation-pareto
  true true true true true true false false
