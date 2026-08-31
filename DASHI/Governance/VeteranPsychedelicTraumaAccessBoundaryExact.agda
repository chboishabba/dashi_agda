module DASHI.Governance.VeteranPsychedelicTraumaAccessBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.TrumpDrugPolicyPsychedelicClassificationBidiExact as TrumpPolicy
import DASHI.Governance.TraumaMemorySublationBoundary as Trauma
import DASHI.Biology.PsychedelicAttractorReweightingBoundary as Psychedelic
import DASHI.Governance.DrugGovernanceIntersectionalAuthorityExact as Intersectional

------------------------------------------------------------------------
-- VETERAN / PTSD / PSYCHEDELIC ACCESS BOUNDARY
--
-- Source-bounded 2026 surface: VA launched psilocybin and MDMA-assisted therapy
-- trials for Veterans, including PTSD-related populations, under the broader
-- Trump-administration psychedelic research/access initiative.  Veteran status
-- can therefore be an actual clinical-priority/gateway coordinate.  It does not
-- by itself prove treatment efficacy, universal access, political virtue, or a
-- complete explanation of trauma.
------------------------------------------------------------------------

data VeteranPsychedelicSurface : Set where
  vaPsilocybinPIVOTSurface
  vaMDMAPTSDTrialSurface
  hhsVaFdaCollaborationSurface
  : VeteranPsychedelicSurface

data AccessAuthority : Set where
  researchParticipationAuthority
  clinicalEvidenceAuthority
  regulatoryAccessAuthority
  universalTreatmentAuthority
  politicalNarrativeAuthority
  : AccessAuthority

record VeteranClinicalPriorityReceipt : Set where
  constructor veteranClinicalPriorityReceipt
  field
    surface : VeteranPsychedelicSurface
    policyReference : String
    trialReference : String
    veteranPriorityObserved : Bool
    veteranPriorityObservedIsTrue : veteranPriorityObserved ≡ true
    efficacyProvenByPriority : Bool
    efficacyProvenByPriorityIsFalse : efficacyProvenByPriority ≡ false
    universalAccessProven : Bool
    universalAccessProvenIsFalse : universalAccessProven ≡ false

open VeteranClinicalPriorityReceipt public

psilocybinPriorityReceipt : VeteranClinicalPriorityReceipt
psilocybinPriorityReceipt = veteranClinicalPriorityReceipt
  vaPsilocybinPIVOTSurface
  "Trump Executive Order, 18 April 2026, accelerates psychedelic research/access for serious mental illness with particular veteran emphasis"
  "VA PIVOT trial announced 5 August 2026: psilocybin for treatment-resistant depression, including concurrent PTSD"
  true refl
  false refl
  false refl

mdmaPriorityReceipt : VeteranClinicalPriorityReceipt
mdmaPriorityReceipt = veteranClinicalPriorityReceipt
  vaMDMAPTSDTrialSurface
  "Trump Executive Order / VA-HHS-FDA psychedelic collaboration"
  "VA randomized MDMA-assisted therapy trial announced 26 May 2026 for PTSD and alcohol use disorder in U.S. Veterans"
  true refl
  false refl
  false refl

trumpPolicyBoundary : TrumpPolicy.TrumpDrugPolicyClassificationBoundary
trumpPolicyBoundary = TrumpPolicy.canonicalTrumpDrugPolicyClassificationBoundary

traumaBoundary : Trauma.TraumaMemorySublationBoundary
traumaBoundary = Trauma.canonicalTraumaMemorySublationBoundary

psychedelicBoundary : Psychedelic.PsychedelicAttractorBoundary
psychedelicBoundary = Psychedelic.canonicalPsychedelicAttractorBoundary

intersectionalBoundary : Intersectional.DrugGovernanceIntersectionalBoundary
intersectionalBoundary = Intersectional.canonicalDrugGovernanceIntersectionalBoundary

------------------------------------------------------------------------
-- Veteran status is a real route coordinate, but not a complete moral or
-- epistemic ordering over other trauma/drug-affected populations.
------------------------------------------------------------------------

data VeteranPriorityPromotesEfficacy : Set where

data VeteranPriorityPromotesMoralPriority : Set where

data PTSDDiagnosisPromotesRecoveredMemory : Set where

data PsychedelicTrialPromotesWarOnDrugsResolution : Set where

veteranPriorityDoesNotPromoteEfficacy : VeteranPriorityPromotesEfficacy → ⊥
veteranPriorityDoesNotPromoteEfficacy ()

veteranPriorityDoesNotPromoteMoralPriority :
  VeteranPriorityPromotesMoralPriority → ⊥
veteranPriorityDoesNotPromoteMoralPriority ()

ptsdDoesNotPromoteRecoveredMemory : PTSDDiagnosisPromotesRecoveredMemory → ⊥
ptsdDoesNotPromoteRecoveredMemory ()

trialDoesNotPromoteWarOnDrugsResolution :
  PsychedelicTrialPromotesWarOnDrugsResolution → ⊥
trialDoesNotPromoteWarOnDrugsResolution ()

record VeteranPsychedelicTraumaAccessBoundary : Set where
  constructor veteranPsychedelicTraumaAccessBoundary
  field
    veteranStatusCanBeClinicalPriorityCoordinate : Bool
    veteranStatusCanBeClinicalPriorityCoordinateIsTrue :
      veteranStatusCanBeClinicalPriorityCoordinate ≡ true
    veteranPriorityProvesTreatmentEfficacy : Bool
    veteranPriorityProvesTreatmentEfficacyIsFalse :
      veteranPriorityProvesTreatmentEfficacy ≡ false
    veteranPriorityEstablishesUniversalAccess : Bool
    veteranPriorityEstablishesUniversalAccessIsFalse :
      veteranPriorityEstablishesUniversalAccess ≡ false
    PTSDLabelRecoversCompleteTraumaHistory : Bool
    PTSDLabelRecoversCompleteTraumaHistoryIsFalse :
      PTSDLabelRecoversCompleteTraumaHistory ≡ false
    psychedelicAccessForVeteransEndsPunitiveDrugGovernance : Bool
    psychedelicAccessForVeteransEndsPunitiveDrugGovernanceIsFalse :
      psychedelicAccessForVeteransEndsPunitiveDrugGovernance ≡ false

canonicalVeteranPsychedelicTraumaAccessBoundary :
  VeteranPsychedelicTraumaAccessBoundary
canonicalVeteranPsychedelicTraumaAccessBoundary =
  veteranPsychedelicTraumaAccessBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
