module DASHI.Cognition.ClinicToStreetsConsumerCrosswalkExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.ClinicToStreetsSOTAEvidenceAtlasExact as SOTA
import DASHI.Cognition.ClinicToStreetsIntersectionalityReuseExact as Intersectionality

------------------------------------------------------------------------
-- CONSUMER-RELATIVE APPROACH CROSSWALK
--
-- This is a comparison surface, not a new clinical ontology and not an
-- efficacy ranking.  It records which downstream consumers each surrounding
-- approach is designed to speak to, while retaining source/evidence ceilings.
------------------------------------------------------------------------

data Approach : Set where
  culturalFormulationInterview : Approach
  mappingVulnerabilityPrivilege : Approach
  socialDeterminantsCounseling : Approach
  criticalLiberationPsychotherapy : Approach
  clinicToStreetsTheory : Approach

data Consumer : Set where
  diagnosisConsumer : Consumer
  formulationConsumer : Consumer
  treatmentPlanningConsumer : Consumer
  materialSocialReferralConsumer : Consumer
  selfBlameAttributionConsumer : Consumer
  representedIndividualAgencyConsumer : Consumer
  representedCollectiveAgencyConsumer : Consumer
  patientAuthoredRelevanceConsumer : Consumer
  therapeuticAllianceConsumer : Consumer
  implementationFidelityConsumer : Consumer
  actualBehaviourConsumer : Consumer
  patientMaterialOutcomeConsumer : Consumer

approaches : List Approach
approaches =
  culturalFormulationInterview ∷
  mappingVulnerabilityPrivilege ∷
  socialDeterminantsCounseling ∷
  criticalLiberationPsychotherapy ∷
  clinicToStreetsTheory ∷ []

consumers : List Consumer
consumers =
  diagnosisConsumer ∷
  formulationConsumer ∷
  treatmentPlanningConsumer ∷
  materialSocialReferralConsumer ∷
  selfBlameAttributionConsumer ∷
  representedIndividualAgencyConsumer ∷
  representedCollectiveAgencyConsumer ∷
  patientAuthoredRelevanceConsumer ∷
  therapeuticAllianceConsumer ∷
  implementationFidelityConsumer ∷
  actualBehaviourConsumer ∷
  patientMaterialOutcomeConsumer ∷ []

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

approachCount : Nat
approachCount = length approaches

consumerCount : Nat
consumerCount = length consumers

------------------------------------------------------------------------
-- Declared relevance, not comparative efficacy.
------------------------------------------------------------------------

data RelevanceStatus : Set where
  primaryDeclaredConsumer : RelevanceStatus
  secondaryDeclaredConsumer : RelevanceStatus
  empiricalConsumerUnpaid : RelevanceStatus
  notClaimedHere : RelevanceStatus

relevance : Approach → Consumer → RelevanceStatus
relevance culturalFormulationInterview diagnosisConsumer = primaryDeclaredConsumer
relevance culturalFormulationInterview formulationConsumer = primaryDeclaredConsumer
relevance culturalFormulationInterview treatmentPlanningConsumer = primaryDeclaredConsumer
relevance culturalFormulationInterview patientAuthoredRelevanceConsumer = secondaryDeclaredConsumer
relevance culturalFormulationInterview therapeuticAllianceConsumer = secondaryDeclaredConsumer
relevance culturalFormulationInterview implementationFidelityConsumer = empiricalConsumerUnpaid
relevance culturalFormulationInterview actualBehaviourConsumer = empiricalConsumerUnpaid
relevance culturalFormulationInterview patientMaterialOutcomeConsumer = empiricalConsumerUnpaid
relevance culturalFormulationInterview _ = notClaimedHere

relevance mappingVulnerabilityPrivilege formulationConsumer = primaryDeclaredConsumer
relevance mappingVulnerabilityPrivilege treatmentPlanningConsumer = primaryDeclaredConsumer
relevance mappingVulnerabilityPrivilege materialSocialReferralConsumer = primaryDeclaredConsumer
relevance mappingVulnerabilityPrivilege selfBlameAttributionConsumer = secondaryDeclaredConsumer
relevance mappingVulnerabilityPrivilege representedIndividualAgencyConsumer = secondaryDeclaredConsumer
relevance mappingVulnerabilityPrivilege representedCollectiveAgencyConsumer = secondaryDeclaredConsumer
relevance mappingVulnerabilityPrivilege patientAuthoredRelevanceConsumer = primaryDeclaredConsumer
relevance mappingVulnerabilityPrivilege implementationFidelityConsumer = empiricalConsumerUnpaid
relevance mappingVulnerabilityPrivilege patientMaterialOutcomeConsumer = empiricalConsumerUnpaid
relevance mappingVulnerabilityPrivilege _ = notClaimedHere

relevance socialDeterminantsCounseling formulationConsumer = primaryDeclaredConsumer
relevance socialDeterminantsCounseling treatmentPlanningConsumer = primaryDeclaredConsumer
relevance socialDeterminantsCounseling materialSocialReferralConsumer = primaryDeclaredConsumer
relevance socialDeterminantsCounseling representedIndividualAgencyConsumer = secondaryDeclaredConsumer
relevance socialDeterminantsCounseling representedCollectiveAgencyConsumer = secondaryDeclaredConsumer
relevance socialDeterminantsCounseling patientAuthoredRelevanceConsumer = secondaryDeclaredConsumer
relevance socialDeterminantsCounseling implementationFidelityConsumer = empiricalConsumerUnpaid
relevance socialDeterminantsCounseling patientMaterialOutcomeConsumer = empiricalConsumerUnpaid
relevance socialDeterminantsCounseling _ = notClaimedHere

relevance criticalLiberationPsychotherapy formulationConsumer = primaryDeclaredConsumer
relevance criticalLiberationPsychotherapy selfBlameAttributionConsumer = primaryDeclaredConsumer
relevance criticalLiberationPsychotherapy representedCollectiveAgencyConsumer = primaryDeclaredConsumer
relevance criticalLiberationPsychotherapy patientAuthoredRelevanceConsumer = secondaryDeclaredConsumer
relevance criticalLiberationPsychotherapy actualBehaviourConsumer = empiricalConsumerUnpaid
relevance criticalLiberationPsychotherapy patientMaterialOutcomeConsumer = empiricalConsumerUnpaid
relevance criticalLiberationPsychotherapy _ = notClaimedHere

relevance clinicToStreetsTheory formulationConsumer = primaryDeclaredConsumer
relevance clinicToStreetsTheory selfBlameAttributionConsumer = primaryDeclaredConsumer
relevance clinicToStreetsTheory representedCollectiveAgencyConsumer = primaryDeclaredConsumer
relevance clinicToStreetsTheory patientAuthoredRelevanceConsumer = secondaryDeclaredConsumer
relevance clinicToStreetsTheory actualBehaviourConsumer = empiricalConsumerUnpaid
relevance clinicToStreetsTheory patientMaterialOutcomeConsumer = empiricalConsumerUnpaid
relevance clinicToStreetsTheory _ = notClaimedHere

------------------------------------------------------------------------
-- Existing intersectionality/situated voice boundary remains the authority.
------------------------------------------------------------------------

affectedConstituencyMayArticulateFurtherAxes : Bool
affectedConstituencyMayArticulateFurtherAxes =
  Intersectionality.affectedConstituencyMayArticulateFurtherAxes

record ClinicConsumerCrosswalkBoundary : Set where
  constructor clinic-consumer-crosswalk-boundary
  field
    crosswalkIsComparativeEfficacyRanking : Bool
    declaredRelevanceCreatesEmpiricalEffect : Bool
    representationalAdequacyImpliesImplementationFidelity : Bool
    implementationFidelityImpliesPatientOutcomeBenefit : Bool
    proxyRepresentationReplacesPatientAuthoredRelevance : Bool
    frameworkAlignmentCreatesComparativeEfficacy : Bool
    oneConsumerMakesApproachUniversallySuperior : Bool
    affectedConstituencyAxesRemainOpen : Bool
    evidenceCeilingsRemainSourceRelative : Bool

open ClinicConsumerCrosswalkBoundary public

canonicalConsumerCrosswalkBoundary : ClinicConsumerCrosswalkBoundary
canonicalConsumerCrosswalkBoundary =
  clinic-consumer-crosswalk-boundary
    false false false false false false false true true

------------------------------------------------------------------------
-- SOTA evidence object remains upstream and non-promoting.
------------------------------------------------------------------------

sotaBoundary : SOTA.ClinicSOTABoundary
sotaBoundary = SOTA.canonicalClinicSOTABoundary

data DeclaredRelevanceProvesOutcome : Set where
data FrameworkAlignmentProvesEfficacy : Set where

declaredRelevanceDoesNotProveOutcome : DeclaredRelevanceProvesOutcome → ⊥
declaredRelevanceDoesNotProveOutcome ()

frameworkAlignmentDoesNotProveEfficacy : FrameworkAlignmentProvesEfficacy → ⊥
frameworkAlignmentDoesNotProveEfficacy ()
