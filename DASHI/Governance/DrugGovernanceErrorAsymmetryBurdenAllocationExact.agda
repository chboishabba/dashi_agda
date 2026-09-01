module DASHI.Governance.DrugGovernanceErrorAsymmetryBurdenAllocationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.DrugGovernanceRepairMandateGateExact as MandateGate
import DASHI.Governance.DrugGovernanceErrorAllocationChillingExact as Error

------------------------------------------------------------------------
-- ASYMMETRIC DRUG-CLASSIFICATION ERROR / BURDEN ALLOCATION
--
-- Error classes are not collapsed into one scalar loss.  A wrongly punitive
-- classification, care denial, authority attribution, commercial legitimacy
-- attribution, and sovereignty override can place different burdens on
-- different carriers and require different evidence, repair, and mandate
-- surfaces.
------------------------------------------------------------------------

data ClassificationErrorKind : Set where
  wrongfulPunitiveClassification
  wrongfulCareDenial
  wrongfulAuthorityAttribution
  wrongfulCommercialLegitimacy
  wrongfulSovereigntyOverride
  : ClassificationErrorKind

data BurdenBearer : Set where
  classifiedPerson
  affectedCommunity
  patientOrCareSeeker
  publicInstitution
  commercialBeneficiary
  indigenousSovereignCommunity
  futureHelpSeeker
  : BurdenBearer

data EvidenceBurden : Set where
  punitiveJustificationEvidence
  careEligibilityEvidence
  classificationAuthorityEvidence
  materialBenefitProvenanceEvidence
  sovereignPermissionAuthorityEvidence
  : EvidenceBurden

data RepairBurden : Set where
  reopenPunitiveClassification
  reassessCareEligibility
  reopenCategoryAuthority
  reopenCommercialBenefitLegitimacy
  restoreSovereignAuthorityBoundary
  : RepairBurden

primaryBearer : ClassificationErrorKind → BurdenBearer
primaryBearer wrongfulPunitiveClassification = classifiedPerson
primaryBearer wrongfulCareDenial = patientOrCareSeeker
primaryBearer wrongfulAuthorityAttribution = affectedCommunity
primaryBearer wrongfulCommercialLegitimacy = affectedCommunity
primaryBearer wrongfulSovereigntyOverride = indigenousSovereignCommunity

evidenceBurden : ClassificationErrorKind → EvidenceBurden
evidenceBurden wrongfulPunitiveClassification = punitiveJustificationEvidence
evidenceBurden wrongfulCareDenial = careEligibilityEvidence
evidenceBurden wrongfulAuthorityAttribution = classificationAuthorityEvidence
evidenceBurden wrongfulCommercialLegitimacy = materialBenefitProvenanceEvidence
evidenceBurden wrongfulSovereigntyOverride = sovereignPermissionAuthorityEvidence

repairBurden : ClassificationErrorKind → RepairBurden
repairBurden wrongfulPunitiveClassification = reopenPunitiveClassification
repairBurden wrongfulCareDenial = reassessCareEligibility
repairBurden wrongfulAuthorityAttribution = reopenCategoryAuthority
repairBurden wrongfulCommercialLegitimacy = reopenCommercialBenefitLegitimacy
repairBurden wrongfulSovereigntyOverride = restoreSovereignAuthorityBoundary

repairProposal : ClassificationErrorKind → MandateGate.DrugRepairProposal
repairProposal wrongfulPunitiveClassification = MandateGate.refineBeforeFault
repairProposal wrongfulCareDenial = MandateGate.widenCapabilityCone
repairProposal wrongfulAuthorityAttribution = MandateGate.reopenCategoryContest
repairProposal wrongfulCommercialLegitimacy = MandateGate.reviseBenefitRouting
repairProposal wrongfulSovereigntyOverride = MandateGate.restoreSovereignAuthorityGate

repairAdmissionDemand :
  (error : ClassificationErrorKind) →
  MandateGate.RepairAdmissionDemand (repairProposal error)
repairAdmissionDemand wrongfulPunitiveClassification =
  MandateGate.refineNeedsClassificationAuthority
repairAdmissionDemand wrongfulCareDenial =
  MandateGate.capabilityRepairNeedsScopedAuthority
repairAdmissionDemand wrongfulAuthorityAttribution =
  MandateGate.contestNeedsMetaRuleAuthority
repairAdmissionDemand wrongfulCommercialLegitimacy =
  MandateGate.benefitRevisionNeedsMaterialGovernanceAuthority
repairAdmissionDemand wrongfulSovereigntyOverride =
  MandateGate.sovereigntyRepairNeedsOriginatingAuthority

------------------------------------------------------------------------
-- Same coarse "classification mistake" observer cannot recover which burden
-- has actually been allocated.
------------------------------------------------------------------------

data ErrorSurface : Set where sameClassificationMistake : ErrorSurface

errorSurface : ClassificationErrorKind → ErrorSurface
errorSurface _ = sameClassificationMistake

punitiveVsCareBurdenDiffers :
  primaryBearer wrongfulPunitiveClassification
  ≡ primaryBearer wrongfulCareDenial → ⊥
punitiveVsCareBurdenDiffers ()

commercialVsSovereigntyBurdenDiffers :
  primaryBearer wrongfulCommercialLegitimacy
  ≡ primaryBearer wrongfulSovereigntyOverride → ⊥
commercialVsSovereigntyBurdenDiffers ()

coarseErrorCannotRecoverBearer :
  INF.FactorsThrough errorSurface primaryBearer → ⊥
coarseErrorCannotRecoverBearer =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      wrongfulPunitiveClassification
      wrongfulCareDenial
      refl
      punitiveVsCareBurdenDiffers)

------------------------------------------------------------------------
-- Burden placement itself is not fault or moral desert.
------------------------------------------------------------------------

data BearsBurdenPromotesFault : Set where

data ErrorKindPromotesUniqueRepair : Set where

data EvidenceBurdenPromotesMandate : Set where

data RepairBurdenPromotesGuaranteedRedress : Set where

data CommercialBenefitPromotesLegitimacy : Set where

bearingBurdenDoesNotPromoteFault : BearsBurdenPromotesFault → ⊥
bearingBurdenDoesNotPromoteFault ()

errorKindDoesNotPromoteUniqueRepair : ErrorKindPromotesUniqueRepair → ⊥
errorKindDoesNotPromoteUniqueRepair ()

evidenceBurdenDoesNotPromoteMandate : EvidenceBurdenPromotesMandate → ⊥
evidenceBurdenDoesNotPromoteMandate ()

repairBurdenDoesNotPromoteGuaranteedRedress :
  RepairBurdenPromotesGuaranteedRedress → ⊥
repairBurdenDoesNotPromoteGuaranteedRedress ()

commercialBenefitDoesNotPromoteLegitimacy :
  CommercialBenefitPromotesLegitimacy → ⊥
commercialBenefitDoesNotPromoteLegitimacy ()

------------------------------------------------------------------------
-- Existing chilling owner retained: wrongful punitive/fault routing can impose
-- a downstream future-help-seeking burden independently of fine-rule learning.
------------------------------------------------------------------------

errorAllocationBoundary : Error.DrugGovernanceErrorAllocationBoundary
errorAllocationBoundary = Error.canonicalDrugGovernanceErrorAllocationBoundary

record ErrorAsymmetryBurdenBoundary : Set where
  constructor errorAsymmetryBurdenBoundary
  field
    allClassificationErrorsShareOneBurden : Bool
    allClassificationErrorsShareOneBurdenIsFalse :
      allClassificationErrorsShareOneBurden ≡ false
    errorKindDeterminesEvidenceBurden : Bool
    errorKindDeterminesEvidenceBurdenIsTrue :
      errorKindDeterminesEvidenceBurden ≡ true
    errorKindDeterminesBackwardRepairDemand : Bool
    errorKindDeterminesBackwardRepairDemandIsTrue :
      errorKindDeterminesBackwardRepairDemand ≡ true
    identifyingBurdenSelfIssuesMandate : Bool
    identifyingBurdenSelfIssuesMandateIsFalse :
      identifyingBurdenSelfIssuesMandate ≡ false
    burdenBearerEqualsFaultBearer : Bool
    burdenBearerEqualsFaultBearerIsFalse :
      burdenBearerEqualsFaultBearer ≡ false

canonicalErrorAsymmetryBurdenBoundary : ErrorAsymmetryBurdenBoundary
canonicalErrorAsymmetryBurdenBoundary =
  errorAsymmetryBurdenBoundary
    false refl true refl true refl false refl false refl
