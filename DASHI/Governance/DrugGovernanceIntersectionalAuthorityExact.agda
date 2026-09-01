module DASHI.Governance.DrugGovernanceIntersectionalAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Indigenous
import DASHI.Governance.TrumpDrugPolicyPsychedelicClassificationBidiExact as TrumpPolicy

------------------------------------------------------------------------
-- INTERSECTIONAL DRUG-GOVERNANCE AUTHORITY
--
-- Substance/experience identity does not by itself determine governance status.
-- Carrier position, institutional recognition, medical/veteran status,
-- commercial route, policing context and Indigenous authority can change the
-- legal/epistemic/clinical route.  This is a structural classification assay,
-- not a claim that all groups experience the same burdens or benefits.
------------------------------------------------------------------------

data CarrierPosition : Set where
  criminalizedIllicitCarrier
  veteranTrialParticipant
  regulatedMedicalPatient
  commercialConsumer
  indigenousCeremonialCarrier
  externalBiomedicalResearcher
  : CarrierPosition

data GovernanceStanding : Set where
  punitiveStanding
  clinicalResearchStanding
  regulatedTherapeuticStanding
  consumerMarketStanding
  sovereignCeremonialStanding
  externalObserverStanding
  : GovernanceStanding

data PsychoactiveSurface : Set where
  sameBroadPsychoactiveDomain : PsychoactiveSurface

carrierSurface : CarrierPosition → PsychoactiveSurface
carrierSurface _ = sameBroadPsychoactiveDomain

governanceStanding : CarrierPosition → GovernanceStanding
governanceStanding criminalizedIllicitCarrier = punitiveStanding
governanceStanding veteranTrialParticipant = clinicalResearchStanding
governanceStanding regulatedMedicalPatient = regulatedTherapeuticStanding
governanceStanding commercialConsumer = consumerMarketStanding
governanceStanding indigenousCeremonialCarrier = sovereignCeremonialStanding
governanceStanding externalBiomedicalResearcher = externalObserverStanding

standingDiffers :
  governanceStanding criminalizedIllicitCarrier
  ≡ governanceStanding veteranTrialParticipant → ⊥
standingDiffers ()

samePsychoactiveSurfaceCannotRecoverGovernanceStanding :
  INF.FactorsThrough carrierSurface governanceStanding → ⊥
samePsychoactiveSurfaceCannotRecoverGovernanceStanding =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      criminalizedIllicitCarrier
      veteranTrialParticipant
      refl
      standingDiffers)

indigenousAuthorityBoundary : Indigenous.IndigenousAuthorityEnvelopeBoundary
indigenousAuthorityBoundary = Indigenous.canonicalIndigenousAuthorityEnvelopeBoundary

trumpClassificationBoundary : TrumpPolicy.TrumpDrugPolicyClassificationBoundary
trumpClassificationBoundary =
  TrumpPolicy.canonicalTrumpDrugPolicyClassificationBoundary

------------------------------------------------------------------------
-- Therapeutic or biomedical recognition does not absorb Indigenous authority.
------------------------------------------------------------------------

data BiomedicalApprovalPromotesCeremonialAuthority : Set where

data CeremonialUsePromotesBiomedicalEfficacy : Set where

data VeteranPriorityPromotesUniversalAccess : Set where

biomedicalApprovalDoesNotPromoteCeremonialAuthority :
  BiomedicalApprovalPromotesCeremonialAuthority → ⊥
biomedicalApprovalDoesNotPromoteCeremonialAuthority ()

ceremonialUseDoesNotPromoteBiomedicalEfficacy :
  CeremonialUsePromotesBiomedicalEfficacy → ⊥
ceremonialUseDoesNotPromoteBiomedicalEfficacy ()

veteranPriorityDoesNotPromoteUniversalAccess :
  VeteranPriorityPromotesUniversalAccess → ⊥
veteranPriorityDoesNotPromoteUniversalAccess ()

record DrugGovernanceIntersectionalBoundary : Set where
  constructor drugGovernanceIntersectionalBoundary
  field
    sameSubstanceDomainCanReceiveDifferentInstitutionalRoutes : Bool
    sameSubstanceDomainCanReceiveDifferentInstitutionalRoutesIsTrue :
      sameSubstanceDomainCanReceiveDifferentInstitutionalRoutes ≡ true
    carrierPositionCanMatterToGovernanceStanding : Bool
    carrierPositionCanMatterToGovernanceStandingIsTrue :
      carrierPositionCanMatterToGovernanceStanding ≡ true
    veteranClinicalPriorityEqualsUniversalTherapeuticAccess : Bool
    veteranClinicalPriorityEqualsUniversalTherapeuticAccessIsFalse :
      veteranClinicalPriorityEqualsUniversalTherapeuticAccess ≡ false
    biomedicalRecognitionTransfersIndigenousSovereignty : Bool
    biomedicalRecognitionTransfersIndigenousSovereigntyIsFalse :
      biomedicalRecognitionTransfersIndigenousSovereignty ≡ false
    ceremonialAuthorityProvesClinicalEfficacy : Bool
    ceremonialAuthorityProvesClinicalEfficacyIsFalse :
      ceremonialAuthorityProvesClinicalEfficacy ≡ false

canonicalDrugGovernanceIntersectionalBoundary :
  DrugGovernanceIntersectionalBoundary
canonicalDrugGovernanceIntersectionalBoundary =
  drugGovernanceIntersectionalBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
