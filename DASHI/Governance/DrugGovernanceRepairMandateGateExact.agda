module DASHI.Governance.DrugGovernanceRepairMandateGateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.AuthorityMandateCore as Mandate
import DASHI.Governance.ObserverValuationAuthoritySeparationExact as Authority
import DASHI.Governance.DrugGovernanceErrorAllocationChillingExact as Error
import DASHI.Governance.DrugGovernanceCapabilityFunctioningExact as Capability

------------------------------------------------------------------------
-- DRUG CLASSIFICATION REPAIR / MANDATE GATE
--
-- Detecting a classification defect, evaluating it negatively, identifying a
-- capability loss, or proposing a repair does not self-issue authority to enact
-- that repair.  Institutional modification requires a separately scoped,
-- reviewable and recallable authority relation.
------------------------------------------------------------------------

data DrugClassificationDefect : Set where
  chillingFaultAllocation
  patientVoiceDomestication
  capabilityConeContraction
  authorityMisclassification
  materialBenefitCapture
  sovereigntyErasure
  : DrugClassificationDefect

data DrugRepairProposal : Set where
  refineBeforeFault
  reopenCategoryContest
  widenCapabilityCone
  reviseClassificationRule
  reviseBenefitRouting
  restoreSovereignAuthorityGate
  : DrugRepairProposal

record DefectDiagnosis : Set where
  constructor defectDiagnosis
  field
    defect : DrugClassificationDefect
    evidenceReference : String
    consumerReference : String

record ProposedRepair : Set where
  constructor proposedRepair
  field
    diagnosis : DefectDiagnosis
    proposal : DrugRepairProposal
    predictedCapabilityEffectReference : String
    uncertaintyReference : String

------------------------------------------------------------------------
-- Repair admission is indexed by an independently supplied mandate.
------------------------------------------------------------------------

record MandateGatedRepair
    (mandate : Mandate.Mandate)
    (repair : ProposedRepair) : Set₁ where
  constructor mandateGatedRepair
  field
    authority : Mandate.ScopedAuthority mandate
    scopeMatchesRepair : Set
    scopeMatchesRepairWitness : scopeMatchesRepair
    reviewBeforeActuation : Set
    reviewBeforeActuationWitness : reviewBeforeActuation
    repairDoesNotClaimGuaranteedOutcome : Bool
    repairDoesNotClaimGuaranteedOutcomeIsTrue :
      repairDoesNotClaimGuaranteedOutcome ≡ true

open MandateGatedRepair public

------------------------------------------------------------------------
-- Diagnosis/evaluation/capability analysis cannot manufacture mandate.
------------------------------------------------------------------------

data DefectDiagnosisPromotesMandate : Set where

data NegativeEvaluationPromotesMandate : Set where

data CapabilityLossPromotesMandate : Set where

data ProposedRepairPromotesMandate : Set where

data ForcePromotesMandate : Set where

data ExpertAgreementPromotesConstituencyAuthority : Set where

reportedDefectDoesNotPromoteMandate : DefectDiagnosisPromotesMandate → ⊥
reportedDefectDoesNotPromoteMandate ()

negativeEvaluationDoesNotPromoteMandate : NegativeEvaluationPromotesMandate → ⊥
negativeEvaluationDoesNotPromoteMandate ()

capabilityLossDoesNotPromoteMandate : CapabilityLossPromotesMandate → ⊥
capabilityLossDoesNotPromoteMandate ()

proposalDoesNotPromoteMandate : ProposedRepairPromotesMandate → ⊥
proposalDoesNotPromoteMandate ()

forceDoesNotPromoteMandate : ForcePromotesMandate → ⊥
forceDoesNotPromoteMandate ()

expertAgreementDoesNotPromoteConstituencyAuthority :
  ExpertAgreementPromotesConstituencyAuthority → ⊥
expertAgreementDoesNotPromoteConstituencyAuthority ()

------------------------------------------------------------------------
-- Existing authority separations retained directly.
------------------------------------------------------------------------

canonicalMandateBoundary : Mandate.MandateAuthorityBoundary
canonicalMandateBoundary = Mandate.canonicalMandateAuthorityBoundary

canonicalObserverAuthorityBoundary : Authority.ObserverValuationAuthorityBoundary
canonicalObserverAuthorityBoundary = Authority.canonicalObserverValuationAuthorityBoundary

canonicalErrorBoundary : Error.DrugGovernanceErrorAllocationBoundary
canonicalErrorBoundary = Error.canonicalDrugGovernanceErrorAllocationBoundary

canonicalCapabilityBoundary : Capability.DrugGovernanceCapabilityFunctioningBoundary
canonicalCapabilityBoundary = Capability.canonicalDrugGovernanceCapabilityFunctioningBoundary

------------------------------------------------------------------------
-- BIDI repair gate: forward diagnosis proposes a repair; backward admission
-- demands authority/scope/review receipts before modification can be inhabited.
------------------------------------------------------------------------

data RepairAdmissionDemand : DrugRepairProposal → Set where
  refineNeedsClassificationAuthority : RepairAdmissionDemand refineBeforeFault
  contestNeedsMetaRuleAuthority : RepairAdmissionDemand reopenCategoryContest
  capabilityRepairNeedsScopedAuthority : RepairAdmissionDemand widenCapabilityCone
  ruleRevisionNeedsScopedAuthority : RepairAdmissionDemand reviseClassificationRule
  benefitRevisionNeedsMaterialGovernanceAuthority : RepairAdmissionDemand reviseBenefitRouting
  sovereigntyRepairNeedsOriginatingAuthority : RepairAdmissionDemand restoreSovereignAuthorityGate

record RepairBidiReceipt (proposal : DrugRepairProposal) : Set₁ where
  constructor repairBidiReceipt
  field
    forwardProposal : DrugRepairProposal
    forwardProposalIsSame : forwardProposal ≡ proposal
    backwardDemand : RepairAdmissionDemand proposal
    authorityStillExternallySupplied : Bool
    authorityStillExternallySuppliedIsTrue :
      authorityStillExternallySupplied ≡ true

canonicalSovereigntyRepairDemand :
  RepairBidiReceipt restoreSovereignAuthorityGate
canonicalSovereigntyRepairDemand =
  repairBidiReceipt
    restoreSovereignAuthorityGate refl
    sovereigntyRepairNeedsOriginatingAuthority
    true refl

record DrugGovernanceRepairMandateBoundary : Set where
  constructor drugGovernanceRepairMandateBoundary
  field
    defectDiagnosisSelfIssuesMandate : Bool
    defectDiagnosisSelfIssuesMandateIsFalse :
      defectDiagnosisSelfIssuesMandate ≡ false
    capabilityContractionSelfIssuesMandate : Bool
    capabilityContractionSelfIssuesMandateIsFalse :
      capabilityContractionSelfIssuesMandate ≡ false
    repairProposalSelfIssuesMandate : Bool
    repairProposalSelfIssuesMandateIsFalse :
      repairProposalSelfIssuesMandate ≡ false
    validModificationRequiresScopedAuthority : Bool
    validModificationRequiresScopedAuthorityIsTrue :
      validModificationRequiresScopedAuthority ≡ true
    sovereigntyRepairRequiresIndependentOriginatingAuthority : Bool
    sovereigntyRepairRequiresIndependentOriginatingAuthorityIsTrue :
      sovereigntyRepairRequiresIndependentOriginatingAuthority ≡ true

canonicalDrugGovernanceRepairMandateBoundary :
  DrugGovernanceRepairMandateBoundary
canonicalDrugGovernanceRepairMandateBoundary =
  drugGovernanceRepairMandateBoundary
    false refl false refl false refl true refl true refl
