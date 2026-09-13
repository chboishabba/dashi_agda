module DASHI.Law.SensibLawWoogaroo9281PreclearanceConvergenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawWoogarooPreservationSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- 9281 / 2019-8575 PRECLEARANCE CONVERGENCE
--
-- The local negotiated approval and the proponent's 2019/8575 assessment
-- materials independently converge on the same operational question:
-- federal approval status must be resolved before the relevant clearing phase
-- proceeds. Their legal force is deliberately kept different.
--
-- Snowball rule: acquisition may occur out of dependency order; promotion may
-- not skip source manifestation, same clearing phase, literal instrument, or
-- source force (condition / approved plan / proponent assessment protocol).
------------------------------------------------------------------------

negotiated9281DecisionNotice : Source.AttributedSource
negotiated9281DecisionNotice = Source.mkNoDOISource
  "Ipswich City Council"
  "9281/2024/OW — Negotiated Decision Notice Approval, Kalina Village 2 Stages 1 to 16"
  "Development.i / Ipswich City Council"
  "2026"
  "https://developmenti.ipswich.qld.gov.au/Home/ApplicationDetailsView?appNo=9281%2F2024%2FOW&type=plan_development_apps"
  Source.governmentSource
  "Primary local approval manifestation dated 20 March 2026. It pays the literal assessment-manager conditions and approved-plan manifest, not federal approval status, same-action geometry or commencement."
  Source.publicAttribution

approved9281GeneralArrangement : Source.AttributedSource
approved9281GeneralArrangement = Source.mkNoDOISource
  "Ipswich City Council / Arcadis Australia Pacific Pty Limited"
  "9281/2024/OW approved General Arrangement Plan KV2-AAP-BE-P1-DRG-CI-0061"
  "Approved operational-works plan"
  "2026"
  "https://developmenti.ipswich.qld.gov.au/Home/ApplicationDetailsView?appNo=9281%2F2024%2FOW&type=plan_development_apps"
  Source.governmentSource
  "Council-approved plan manifestation containing the general clearing and earthworks notes. The plan's generic reference to EPBC approval does not identify which Commonwealth instrument applies to which clearing polygon."
  Source.publicAttribution

data SourceForce : Set where
  localApprovalCondition : SourceForce
  councilApprovedPlanNote : SourceForce
  proponentAssessmentProtocol : SourceForce

data PreclearanceCoordinate : Set where
  federalStatusBeforePrestart : PreclearanceCoordinate
  clearingMustFollowEPBCApproval : PreclearanceCoordinate
  environmentalPreclearancePackage : PreclearanceCoordinate
  signedPrestartChecklist : PreclearanceCoordinate
  literalCondition6aSatisfaction : PreclearanceCoordinate
  faunaPreclearanceRecord : PreclearanceCoordinate

record PreclearanceReceipt : Set where
  constructor preclearance-receipt
  field
    coordinate : PreclearanceCoordinate
    sourceForce : SourceForce
    source : Source.AttributedSource
    exactLocator : String
    boundedStatement : String
    primaryManifestationPaid : Bool
    operativePart9Condition : Bool
    paysLiteralFederalInstrument : Bool
    paysCommencement : Bool

open PreclearanceReceipt public

condition6aLocalFederalGate : PreclearanceReceipt
condition6aLocalFederalGate = preclearance-receipt
  federalStatusBeforePrestart
  localApprovalCondition
  negotiated9281DecisionNotice
  "Attachment A, condition 6(a), page 9"
  "Before the prestart meeting the applicant must submit either DCCEEW evidence that the proposed clearing works do not constitute a controlled action under the EPBC Act or a copy of the Commonwealth Approval if the clearing is determined to be a controlled action."
  true false false false

approvedPlanEPBCExecutionGate : PreclearanceReceipt
approvedPlanEPBCExecutionGate = preclearance-receipt
  clearingMustFollowEPBCApproval
  councilApprovedPlanNote
  approved9281GeneralArrangement
  "KV2-AAP-BE-P1-DRG-CI-0061, general clearing and earthworks note 10"
  "The approved plan states that clearing undertaken by the contractor is to be strictly in accordance with the Council-approved vegetation management plan and EPBC approval. The generic phrase does not identify a Commonwealth project number or instrument."
  true false false false

springfield8575EnvironmentalPreclearanceProtocol : PreclearanceReceipt
springfield8575EnvironmentalPreclearanceProtocol = preclearance-receipt
  environmentalPreclearancePackage
  proponentAssessmentProtocol
  Atlas.springfield8575January2026PreliminaryDocumentation
  "Part A section 5.3.3 / MNES Management Plan environmental pre-clearance package"
  "The proponent's 2019/8575 assessment material states that each clearing phase will use an Environmental Pre-Clearance Checklist and Package to ensure required approvals, including EPBC approval requirements relevant to that clearing stage, are compiled and distributed before clearing."
  true false false false

springfield8575SignedChecklistProtocol : PreclearanceReceipt
springfield8575SignedChecklistProtocol = preclearance-receipt
  signedPrestartChecklist
  proponentAssessmentProtocol
  Atlas.springfield8575January2026PreliminaryDocumentation
  "Part A section 5.3.3 / MNES Management Plan signed checklist and project pre-start protocol"
  "The proponent material states that the civil contractor, clearing contractor, fauna spotter catcher, arborist if required, environmental coordinator, superintendent and client sign the checklist before clearing; it is run through at a project pre-start meeting and no clearing for the phase can commence until Environmental Coordinator sign-off."
  true false false false

------------------------------------------------------------------------
-- Convergence is an evidence-routing result, not a transfer of legal force.
------------------------------------------------------------------------

record PreclearanceConvergence : Set where
  constructor preclearance-convergence
  field
    localConditionRequiresFederalStatusResolution : Bool
    approvedPlanReferencesEPBCApprovalForClearing : Bool
    proponentProtocolRequiresApprovalDocumentationBeforeClearing : Bool
    proponentProtocolRequiresSignedPrestartChecklist : Bool
    convergesOnFederalClearanceDependency : Bool
    convertsProponentProtocolIntoFederalApprovalCondition : Bool
    identifiesLiteralCondition6aInstrument : Bool

localConditionAndProponentProtocolConvergeOnFederalClearance : PreclearanceConvergence
localConditionAndProponentProtocolConvergeOnFederalClearance = preclearance-convergence
  true true true true true false false

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data ProponentProtocolEqualsOperativePart9Condition : Set where
data SignedChecklistEqualsFederalApproval : Set where
data ApprovedPlanGenericEPBCNoteIdentifiesInstrument : Set where
data PrestartProtocolPaysActualCommencement : Set where

data SourceCitationPaysSameActionIdentity : Set where

proponentProtocolDoesNotEqualOperativePart9Condition :
  ProponentProtocolEqualsOperativePart9Condition → ⊥
proponentProtocolDoesNotEqualOperativePart9Condition ()

signedChecklistDoesNotEqualFederalApproval : SignedChecklistEqualsFederalApproval → ⊥
signedChecklistDoesNotEqualFederalApproval ()

approvedPlanGenericEPBCNoteDoesNotIdentifyInstrument :
  ApprovedPlanGenericEPBCNoteIdentifiesInstrument → ⊥
approvedPlanGenericEPBCNoteDoesNotIdentifyInstrument ()

prestartProtocolDoesNotPayActualCommencement : PrestartProtocolPaysActualCommencement → ⊥
prestartProtocolDoesNotPayActualCommencement ()

sourceCitationDoesNotPaySameActionIdentity : SourceCitationPaysSameActionIdentity → ⊥
sourceCitationDoesNotPaySameActionIdentity ()

------------------------------------------------------------------------
-- Acquisition leaves. The first leaf can identify the instrument relied on;
-- the second can simultaneously identify the approval documentation actually
-- circulated to the clearing team and provide strong evidence of imminence.
------------------------------------------------------------------------

data AcquisitionStatus : Set where
  acquisitionOpen : AcquisitionStatus
  primaryPaid : AcquisitionStatus

record PreclearanceAcquisitionLeaf : Set where
  constructor preclearance-acquisition-leaf
  field
    coordinate : PreclearanceCoordinate
    exactObject : String
    whyHighAlpha : String
    status : AcquisitionStatus
    mayIdentifyFederalInstrument : Bool
    mayEvidenceImminence : Bool
    conclusionMaySkip : Bool

open PreclearanceAcquisitionLeaf public

condition6aSatisfactionRecordFirstLeaf : PreclearanceAcquisitionLeaf
condition6aSatisfactionRecordFirstLeaf = preclearance-acquisition-leaf
  literalCondition6aSatisfaction
  "The actual 9281/2024/OW condition 6(a) submission accepted by Ipswich before the prestart meeting: DCCEEW no-controlled-action evidence or the literal Commonwealth approval relied upon for the proposed clearing works."
  "It directly answers which Commonwealth instrument, if any, Council was given for the 9281 clearing works and prevents transfer from unrelated Springfield approvals."
  acquisitionOpen true true false

signedEnvironmentalPreclearancePackageSecondLeaf : PreclearanceAcquisitionLeaf
signedEnvironmentalPreclearancePackageSecondLeaf = preclearance-acquisition-leaf
  signedPrestartChecklist
  "The stage-specific Environmental Pre-Clearance Checklist and Package, including approval documents attached or referenced, signatures, date, clearing phase and Environmental Coordinator sign-off."
  "The proponent's 2019/8575 process says this object assembles EPBC approval requirements and is signed at pre-start before clearing. If same-phase identity is paid, it can expose both the federal instrument circulated and a much stronger imminence coordinate."
  acquisitionOpen true true false

faunaPreclearancePlanThirdLeaf : PreclearanceAcquisitionLeaf
faunaPreclearancePlanThirdLeaf = preclearance-acquisition-leaf
  faunaPreclearanceRecord
  "9281 condition 9 spotter-catcher identity/licence and Pre-Clearance Fauna Management Plan supplied before the prestart meeting."
  "This is an independent local prestart producer that can date and identify the clearing phase, but it does not itself identify Commonwealth approval."
  acquisitionOpen false true false

preclearanceAcquisitionOrder : List PreclearanceAcquisitionLeaf
preclearanceAcquisitionOrder =
  condition6aSatisfactionRecordFirstLeaf ∷
  signedEnvironmentalPreclearancePackageSecondLeaf ∷
  faunaPreclearancePlanThirdLeaf ∷
  []

record PreclearanceConvergencePareto : Set where
  constructor preclearance-convergence-pareto
  field
    condition6aLiteralRecordFirst : Bool
    signedPackageSecond : Bool
    sameClearingPhaseBeforeConvergence : Bool
    localConditionKeptDistinctFromProponentProtocol : Bool
    genericEPBCReferenceMayIdentifyInstrument : Bool
    signedChecklistMaySubstituteForApproval : Bool
    acquisitionMayRunOutOfOrder : Bool
    conclusionMaySkipDependencies : Bool

canonicalPreclearanceConvergencePareto : PreclearanceConvergencePareto
canonicalPreclearanceConvergencePareto = preclearance-convergence-pareto
  true true true true false false true false
