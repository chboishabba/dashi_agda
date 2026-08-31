module DASHI.Governance.DrugGovernanceUncertaintyBurdenMandateBidiExact where

open import DASHI.Core.Prelude

import DASHI.Governance.OptionConeCoercionExact as OptionCone
import DASHI.Governance.DrugGovernanceErrorAsymmetryBurdenAllocationExact as Burden
import DASHI.Governance.DrugGovernanceErrorAsymmetryOptionConeExact as Cone
import DASHI.Governance.DrugGovernanceRepairMandateGateExact as MandateGate
import DASHI.Governance.DrugGovernanceFarCrossPollinationCapstoneExact as Far

------------------------------------------------------------------------
-- UNCERTAINTY BURDEN / MANDATE BIDI GATE
--
-- DASHI governance design rule, not a claim about universal positive law:
-- before exercising a contested classification power, the acting institution
-- must discharge the evidence/authority burden indexed by the kind of error it
-- risks imposing.  The rule allocates an obligation to justify action; it does
-- not prove the action correct, fair, or legally valid in a live jurisdiction.
------------------------------------------------------------------------

data ContestedPower : Set where
  imposePunitiveClassification
  denyCareRoute
  assertCategoryAuthority
  assertCommercialLegitimacy
  overrideSovereignStanding
  : ContestedPower

powerForError : Burden.ClassificationErrorKind → ContestedPower
powerForError Burden.wrongfulPunitiveClassification = imposePunitiveClassification
powerForError Burden.wrongfulCareDenial = denyCareRoute
powerForError Burden.wrongfulAuthorityAttribution = assertCategoryAuthority
powerForError Burden.wrongfulCommercialLegitimacy = assertCommercialLegitimacy
powerForError Burden.wrongfulSovereigntyOverride = overrideSovereignStanding

data BurdenHolder : Set where
  punitiveClassifierInstitution
  careGatekeepingInstitution
  categoryClaimingInstitution
  commercialLegitimacyClaimant
  externalSovereigntyOverrideActor
  : BurdenHolder

burdenHolder : Burden.ClassificationErrorKind → BurdenHolder
burdenHolder Burden.wrongfulPunitiveClassification = punitiveClassifierInstitution
burdenHolder Burden.wrongfulCareDenial = careGatekeepingInstitution
burdenHolder Burden.wrongfulAuthorityAttribution = categoryClaimingInstitution
burdenHolder Burden.wrongfulCommercialLegitimacy = commercialLegitimacyClaimant
burdenHolder Burden.wrongfulSovereigntyOverride = externalSovereigntyOverrideActor

record PreActuationBurden (error : Burden.ClassificationErrorKind) : Set where
  constructor preActuationBurden
  field
    actingPower : ContestedPower
    actingPowerIsIndexed : actingPower ≡ powerForError error
    holder : BurdenHolder
    holderIsIndexed : holder ≡ burdenHolder error
    evidenceRequired : Burden.EvidenceBurden
    evidenceIsIndexed : evidenceRequired ≡ Burden.evidenceBurden error
    repairDemandIfErrorMaterialises :
      MandateGate.RepairAdmissionDemand (Burden.repairProposal error)
    burdenDischargeDoesNotGuaranteeCorrectness : Bool
    burdenDischargeDoesNotGuaranteeCorrectnessIsTrue :
      burdenDischargeDoesNotGuaranteeCorrectness ≡ true

canonicalPreActuationBurden :
  (error : Burden.ClassificationErrorKind) → PreActuationBurden error
canonicalPreActuationBurden error =
  preActuationBurden
    (powerForError error) refl
    (burdenHolder error) refl
    (Burden.evidenceBurden error) refl
    (Burden.repairAdmissionDemand error)
    true refl

------------------------------------------------------------------------
-- BIDI: forward contemplated power -> indexed risk; backward risk -> evidence
-- burden + possible repair/mandate demand.
------------------------------------------------------------------------

record ErrorBurdenBidiReceipt (error : Burden.ClassificationErrorKind) : Set where
  constructor errorBurdenBidiReceipt
  field
    forwardErrorClass : Burden.ClassificationErrorKind
    forwardErrorClassIsSame : forwardErrorClass ≡ error
    exposedBurdenBearer : Burden.BurdenBearer
    exposedBurdenBearerIsIndexed :
      exposedBurdenBearer ≡ Burden.primaryBearer error
    requiredEvidence : Burden.EvidenceBurden
    requiredEvidenceIsIndexed :
      requiredEvidence ≡ Burden.evidenceBurden error
    backwardRepair : Burden.RepairBurden
    backwardRepairIsIndexed : backwardRepair ≡ Burden.repairBurden error
    backwardMandateDemand :
      MandateGate.RepairAdmissionDemand (Burden.repairProposal error)

canonicalErrorBurdenBidi :
  (error : Burden.ClassificationErrorKind) → ErrorBurdenBidiReceipt error
canonicalErrorBurdenBidi error =
  errorBurdenBidiReceipt
    error refl
    (Burden.primaryBearer error) refl
    (Burden.evidenceBurden error) refl
    (Burden.repairBurden error) refl
    (Burden.repairAdmissionDemand error)

------------------------------------------------------------------------
-- Concrete option-cone receipts make the burden operational.
------------------------------------------------------------------------

punitiveRiskCanContractFutureHelpSeeking :
  OptionCone.StrictSafeReachabilityContraction
    Cone.reachability Cone.baselineWorld Cone.punitiveErrorWorld
punitiveRiskCanContractFutureHelpSeeking = Cone.punitiveErrorContractsHelpSeeking

sovereigntyRiskCanContractCeremonialGovernance :
  OptionCone.StrictSafeReachabilityContraction
    Cone.reachability Cone.baselineWorld Cone.sovereigntyOverrideWorld
sovereigntyRiskCanContractCeremonialGovernance =
  Cone.sovereigntyOverrideContractsGovernance

------------------------------------------------------------------------
-- Far cross-pollination retained: philosophy/power audits can seed which burden
-- to investigate, but cannot discharge the burden themselves.
------------------------------------------------------------------------

farBoundary : Far.DrugGovernanceFarCrossPollinationBoundary
farBoundary = Far.canonicalDrugGovernanceFarCrossPollinationBoundary

data AuditPromotesBurdenDischarge : Set where

data BurdenDischargePromotesMandate : Set where

data MandatePromotesEmpiricalSuccess : Set where

data HigherBurdenPromotesMoralPriority : Set where

auditDoesNotPromoteBurdenDischarge : AuditPromotesBurdenDischarge → ⊥
auditDoesNotPromoteBurdenDischarge ()

burdenDischargeDoesNotPromoteMandate : BurdenDischargePromotesMandate → ⊥
burdenDischargeDoesNotPromoteMandate ()

mandateDoesNotPromoteEmpiricalSuccess : MandatePromotesEmpiricalSuccess → ⊥
mandateDoesNotPromoteEmpiricalSuccess ()

higherBurdenDoesNotPromoteMoralPriority : HigherBurdenPromotesMoralPriority → ⊥
higherBurdenDoesNotPromoteMoralPriority ()

record UncertaintyBurdenMandateBoundary : Set where
  constructor uncertaintyBurdenMandateBoundary
  field
    differentPowersCarryDifferentEvidenceBurdens : Bool
    differentPowersCarryDifferentEvidenceBurdensIsTrue :
      differentPowersCarryDifferentEvidenceBurdens ≡ true
    burdenIsPlacedBeforeContestedActuation : Bool
    burdenIsPlacedBeforeContestedActuationIsTrue :
      burdenIsPlacedBeforeContestedActuation ≡ true
    philosophicalAuditDischargesEvidenceBurden : Bool
    philosophicalAuditDischargesEvidenceBurdenIsFalse :
      philosophicalAuditDischargesEvidenceBurden ≡ false
    satisfyingEvidenceBurdenSelfIssuesMandate : Bool
    satisfyingEvidenceBurdenSelfIssuesMandateIsFalse :
      satisfyingEvidenceBurdenSelfIssuesMandate ≡ false
    mandateGuaranteesSuccessfulRepair : Bool
    mandateGuaranteesSuccessfulRepairIsFalse :
      mandateGuaranteesSuccessfulRepair ≡ false

canonicalUncertaintyBurdenMandateBoundary : UncertaintyBurdenMandateBoundary
canonicalUncertaintyBurdenMandateBoundary =
  uncertaintyBurdenMandateBoundary
    true refl true refl false refl false refl false refl
