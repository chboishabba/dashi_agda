module DASHI.Governance.DrugGovernanceErrorCapabilityMandateBidiCapstoneExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Governance.DrugGovernanceErrorAllocationChillingExact as Error
import DASHI.Governance.DrugPatientCategoryAntiDomesticationExact as AntiDomestication
import DASHI.Governance.DrugGovernanceCapabilityFunctioningExact as Capability
import DASHI.Governance.DrugGovernanceRepairMandateGateExact as MandateGate
import DASHI.Governance.DrugCategoryCostedQuotientDiscriminatorExact as Costed
import DASHI.Governance.DrugGovernanceFiveProbeAdaptivePlannerExact as Planner
import DASHI.Governance.DrugGovernanceFiveProbeWorldExact as Five
import DASHI.Governance.OptionConeCoercionExact as Cone

------------------------------------------------------------------------
-- ERROR / CAPABILITY / MANDATE BIDI CAPSTONE
--
-- Diagnosis directs information acquisition and can identify an operational
-- capability loss.  It can seed a repair proposal.  The backward edge from a
-- repair proposal is not actuation but a mandate/admission demand.
------------------------------------------------------------------------

data GovernanceTrigger : Set where
  unresolvedClassificationTrigger
  chillingAfterFaultTrigger
  admittedVoiceWithoutMetaRuleTrigger
  sameFunctioningDifferentCapabilityTrigger
  materialBenefitAsymmetryTrigger
  sovereigntyErasureTrigger
  : GovernanceTrigger

triggerProbe : GovernanceTrigger → Costed.ProbeKind
triggerProbe unresolvedClassificationTrigger = Costed.historyProbe
triggerProbe chillingAfterFaultTrigger = Costed.authorityProbe
triggerProbe admittedVoiceWithoutMetaRuleTrigger = Costed.authorityProbe
triggerProbe sameFunctioningDifferentCapabilityTrigger = Costed.materialBenefitProbe
triggerProbe materialBenefitAsymmetryTrigger = Costed.materialBenefitProbe
triggerProbe sovereigntyErasureTrigger = Costed.sovereigntyProbe

triggerRepair : GovernanceTrigger → MandateGate.DrugRepairProposal
triggerRepair unresolvedClassificationTrigger = MandateGate.refineBeforeFault
triggerRepair chillingAfterFaultTrigger = MandateGate.widenCapabilityCone
triggerRepair admittedVoiceWithoutMetaRuleTrigger = MandateGate.reopenCategoryContest
triggerRepair sameFunctioningDifferentCapabilityTrigger = MandateGate.widenCapabilityCone
triggerRepair materialBenefitAsymmetryTrigger = MandateGate.reviseBenefitRouting
triggerRepair sovereigntyErasureTrigger = MandateGate.restoreSovereignAuthorityGate

repairDemand :
  (trigger : GovernanceTrigger) →
  MandateGate.RepairAdmissionDemand (triggerRepair trigger)
repairDemand unresolvedClassificationTrigger = MandateGate.refineNeedsClassificationAuthority
repairDemand chillingAfterFaultTrigger = MandateGate.capabilityRepairNeedsScopedAuthority
repairDemand admittedVoiceWithoutMetaRuleTrigger = MandateGate.contestNeedsMetaRuleAuthority
repairDemand sameFunctioningDifferentCapabilityTrigger = MandateGate.capabilityRepairNeedsScopedAuthority
repairDemand materialBenefitAsymmetryTrigger = MandateGate.benefitRevisionNeedsMaterialGovernanceAuthority
repairDemand sovereigntyErasureTrigger = MandateGate.sovereigntyRepairNeedsOriginatingAuthority

record GovernanceBidiCycle (trigger : GovernanceTrigger) : Set where
  constructor governanceBidiCycle
  field
    forwardDiagnosticTrigger : GovernanceTrigger
    triggerIsSame : forwardDiagnosticTrigger ≡ trigger
    candidateProbe : Costed.ProbeKind
    candidateProbeIsMapped : candidateProbe ≡ triggerProbe trigger
    proposedRepair : MandateGate.DrugRepairProposal
    proposedRepairIsMapped : proposedRepair ≡ triggerRepair trigger
    backwardAdmissionDemand : MandateGate.RepairAdmissionDemand proposedRepair
    actuationAuthorityNotManufactured : Bool
    actuationAuthorityNotManufacturedIsTrue :
      actuationAuthorityNotManufactured ≡ true

canonicalCycle : (trigger : GovernanceTrigger) → GovernanceBidiCycle trigger
canonicalCycle trigger =
  governanceBidiCycle
    trigger refl
    (triggerProbe trigger) refl
    (triggerRepair trigger) refl
    (repairDemand trigger)
    true refl

------------------------------------------------------------------------
-- Concrete operational receipts retained from the component owners.
------------------------------------------------------------------------

faultAllocationReallyContractsHelpSeeking :
  Cone.StrictSafeReachabilityContraction
    Error.drugReachability Error.beforeAllocation Error.faultResponse
faultAllocationReallyContractsHelpSeeking = Error.faultAllocationContractsHelpSeeking

admittedPatientVoiceStillLacksAutomaticMetaRulePower :
  AntiDomestication.CanAlterDrugCategoryAdmissionRule
    AntiDomestication.admittedPatientVoice → ⊥
admittedPatientVoiceStillLacksAutomaticMetaRulePower =
  AntiDomestication.admittedPatientVoiceCannotSelfIssueMetaRulePower

sameTreatmentStillCannotRecoverCapability :
  INF.FactorsThrough Capability.functioning Capability.capability → ⊥
sameTreatmentStillCannotRecoverCapability = Capability.functioningCannotRecoverCapability

sovereigntyProbeHasLivePlanner :
  Sequential.SequentialConsumerPlan
    Five.sovereigntyPosition
    (Planner.allCompatible tt)
sovereigntyProbeHasLivePlanner = Planner.sovereigntyPlan

------------------------------------------------------------------------
-- Non-promotion barriers.
------------------------------------------------------------------------

data DiagnosisPromotesCorrectRepair : Set where

data ProbePromotesMandate : Set where

data CapabilityDifferencePromotesNormativeVerdict : Set where

data MandatePromotesGuaranteedOutcome : Set where

diagnosisDoesNotPromoteCorrectRepair : DiagnosisPromotesCorrectRepair → ⊥
diagnosisDoesNotPromoteCorrectRepair ()

probeDoesNotPromoteMandate : ProbePromotesMandate → ⊥
probeDoesNotPromoteMandate ()

capabilityDifferenceDoesNotPromoteNormativeVerdict :
  CapabilityDifferencePromotesNormativeVerdict → ⊥
capabilityDifferenceDoesNotPromoteNormativeVerdict ()

mandateDoesNotPromoteGuaranteedOutcome : MandatePromotesGuaranteedOutcome → ⊥
mandateDoesNotPromoteGuaranteedOutcome ()

record ErrorCapabilityMandateBidiBoundary : Set where
  constructor errorCapabilityMandateBidiBoundary
  field
    diagnosticTriggerCanSeedProbe : Bool
    diagnosticTriggerCanSeedProbeIsTrue : diagnosticTriggerCanSeedProbe ≡ true
    probeCanExposeCapabilityRelevantDifference : Bool
    probeCanExposeCapabilityRelevantDifferenceIsTrue :
      probeCanExposeCapabilityRelevantDifference ≡ true
    diagnosedCapabilityLossSelfIssuesRepairMandate : Bool
    diagnosedCapabilityLossSelfIssuesRepairMandateIsFalse :
      diagnosedCapabilityLossSelfIssuesRepairMandate ≡ false
    admittedVoiceAutomaticallyOwnsMetaRule : Bool
    admittedVoiceAutomaticallyOwnsMetaRuleIsFalse :
      admittedVoiceAutomaticallyOwnsMetaRule ≡ false
    mandateGuaranteesDesiredFunctioning : Bool
    mandateGuaranteesDesiredFunctioningIsFalse :
      mandateGuaranteesDesiredFunctioning ≡ false

canonicalErrorCapabilityMandateBidiBoundary : ErrorCapabilityMandateBidiBoundary
canonicalErrorCapabilityMandateBidiBoundary =
  errorCapabilityMandateBidiBoundary
    true refl true refl false refl false refl false refl
