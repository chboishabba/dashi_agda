module DASHI.Law.SensibLawWoogaroo9281FederalPrestartGateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 9281/2024/OW NEGOTIATED DECISION: FEDERAL / PRESTART EXECUTION GATES
--
-- Source manifestation: Ipswich City Council Negotiated Decision Notice,
-- 20 March 2026, plus approved plans supplied in the application archive.
-- This owner records only the literal local conditions.  It does not promote
-- parcel identity into EPBC same-object geometry or a prestart filing into
-- actual commencement.
------------------------------------------------------------------------

data GateKind : Set where
  federalClearance : GateKind
  faunaPreclearance : GateKind
  councilLandLicence : GateKind
  arboriculturalPreclearance : GateKind

data GateStatus : Set where
  primaryPaid : GateStatus
  acquisitionOpen : GateStatus

record LocalExecutionGate : Set where
  constructor local-execution-gate
  field
    kind : GateKind
    exactLocator : String
    boundedStatement : String
    status : GateStatus
    importsCommencement : Bool
    importsCommencementIsFalse : importsCommencement ≡ false

open LocalExecutionGate public

condition6aFederalClearanceBeforePrestart : LocalExecutionGate
condition6aFederalClearanceBeforePrestart = local-execution-gate
  federalClearance
  "9281/2024/OW Negotiated Decision Notice, Attachment A, condition 6(a)"
  "Before the prestart meeting the applicant must submit either DCCEEW evidence that the proposed clearing works are not a controlled action under the EPBC Act, or a copy of the Commonwealth Approval if the clearing is determined to be a controlled action."
  primaryPaid false refl

condition9LicensedSpotterCatcher : LocalExecutionGate
condition9LicensedSpotterCatcher = local-execution-gate
  faunaPreclearance
  "9281/2024/OW Negotiated Decision Notice, Attachment A, condition 9(a)-(c)"
  "A licensed spotter catcher must assess the site, supervise vegetation removal and deal with native fauna; name, licence numbers and contact details must be supplied to Council before the prestart meeting and displayed on the site sign."
  primaryPaid false refl

condition9PreClearanceFaunaPlan : LocalExecutionGate
condition9PreClearanceFaunaPlan = local-execution-gate
  faunaPreclearance
  "9281/2024/OW Negotiated Decision Notice, Attachment A, condition 9(d)"
  "A Pre-Clearance Fauna Management Plan prepared by the appointed spotter catcher must be submitted to the assessment manager before the prestart meeting."
  primaryPaid false refl

councilLandAccessLicenceGate : LocalExecutionGate
councilLandAccessLicenceGate = local-execution-gate
  councilLandLicence
  "9281/2024/OW Negotiated Decision Notice, advice concerning Council-controlled land"
  "An Access and Works Licence Agreement must be granted by Council before works commence on Council-controlled land."
  primaryPaid false refl

arboriculturalTenMetreGate : LocalExecutionGate
arboriculturalTenMetreGate = local-execution-gate
  arboriculturalPreclearance
  "9281/2024/OW Negotiated Decision Notice, condition 8(a)-(c), as negotiated 20 March 2026"
  "An arboricultural impact assessment and protection measures are required before clearing within ten metres of open-space areas; the negotiated decision changed the timing from prestart to the commencement of such clearing."
  primaryPaid false refl

------------------------------------------------------------------------
-- EPBC branch logic and attribution firewalls.
------------------------------------------------------------------------

record ControlledActionBranch : Set where
  constructor controlled-action-branch
  field
    projectKnownControlledAction : Bool
    sameObjectClearingYetPaid : Bool
    noControlledActionCertificateCanSubstituteIfSameObjectPaid : Bool
    commonwealthApprovalBecomesLocalPrestartPaymentIfSameObjectPaid : Bool

controlledActionBranchMakesApprovalLeafCritical : ControlledActionBranch
controlledActionBranchMakesApprovalLeafCritical = controlled-action-branch
  true false true true

data LocalConditionPaysSameObjectGeometry : Set where
data FaunaPlanPaysCommencement : Set where
data ApprovedPlansPayFederalApproval : Set where

localConditionDoesNotPaySameObjectGeometry : LocalConditionPaysSameObjectGeometry → ⊥
localConditionDoesNotPaySameObjectGeometry ()

faunaPlanDoesNotPayCommencement : FaunaPlanPaysCommencement → ⊥
faunaPlanDoesNotPayCommencement ()

approvedPlansDoNotPayFederalApproval : ApprovedPlansPayFederalApproval → ⊥
approvedPlansDoNotPayFederalApproval ()

------------------------------------------------------------------------
-- Highest-alpha producer set for imminence.
------------------------------------------------------------------------

data ImminenceProducer : Set where
  commonwealthApprovalOrDCCEEWReceipt : ImminenceProducer
  prestartMeetingRecord : ImminenceProducer
  spotterCatcherIdentityAndLicence : ImminenceProducer
  preClearanceFaunaManagementPlan : ImminenceProducer
  arboriculturalImpactAssessment : ImminenceProducer
  accessAndWorksLicence : ImminenceProducer
  contractorSiteSign : ImminenceProducer

firstImminenceProducerSet : List ImminenceProducer
firstImminenceProducerSet =
  commonwealthApprovalOrDCCEEWReceipt ∷
  prestartMeetingRecord ∷
  spotterCatcherIdentityAndLicence ∷
  preClearanceFaunaManagementPlan ∷
  arboriculturalImpactAssessment ∷
  accessAndWorksLicence ∷
  contractorSiteSign ∷
  []
