module DASHI.Cognition.KirkVilyaCounterfactualPreventionBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.CharlieKirkAssassinationEvidenceSpeculationBoundaryExact as Kirk
import DASHI.Cognition.VilyaProtectionSourceAtlasExact as Vilya

------------------------------------------------------------------------
-- KIRK / UVU RETROSPECTIVE COUNTERFACTUAL BOUNDARY
--
-- The official UVU after-action review supplies a retrospective operational
-- failure surface: elevated-vantage/building-access risk was not formalised in
-- a comprehensive assessment, no joint pre-event security walkthrough took
-- place, and existing camera/security technology was not effectively fused
-- into real-time awareness.
--
-- Those findings overlap with the classes of questions VILYA publicly claims
-- to support.  Overlap pays capability relevance only.  It does not establish
-- that VILYA would have been used correctly, that mitigation would have been
-- adopted, that the attacker could not adapt, or that Kirk would have lived.
------------------------------------------------------------------------

data UVUProtectiveOmission : Set where
  noComprehensiveWrittenAssessment : UVUProtectiveOmission
  elevatedVantageRiskNotFormalised : UVUProtectiveOmission
  noJointSecurityWalkthrough : UVUProtectiveOmission
  cameraAwarenessNotOperationallyIntegrated : UVUProtectiveOmission

data CounterfactualStage : Set where
  representVulnerability : CounterfactualStage
  operatorNoticesFinding : CounterfactualStage
  findingTrusted : CounterfactualStage
  authorityAcceptsMitigation : CounterfactualStage
  mitigationImplemented : CounterfactualStage
  adversaryDoesNotAdapt : CounterfactualStage
  harmPrevented : CounterfactualStage

record CounterfactualLinkDemand : Set where
  constructor counterfactual-link-demand
  field
    fromStage : CounterfactualStage
    toStage : CounterfactualStage
    sameEventReference : String
    interventionReference : String
    comparatorReference : String
    outcomeReference : String
    identificationReference : String

open CounterfactualLinkDemand public

kirkPhysicalEventBoundary : Kirk.KirkEvidenceBoundary
kirkPhysicalEventBoundary = Kirk.canonicalKirkEvidenceBoundary

relevantProtectiveObservableOmissionPaid : Bool
relevantProtectiveObservableOmissionPaid = true

vilyaCapabilityAddressesSightlineClass : Bool
vilyaCapabilityAddressesSightlineClass = true

vilyaCapabilityAddressesCameraCoverageClass : Bool
vilyaCapabilityAddressesCameraCoverageClass = true

capabilityAddressesOmittedObservableImpliesPrevention : Bool
capabilityAddressesOmittedObservableImpliesPrevention = false

vilyaWouldHavePreventedKirkPaid : Bool
vilyaWouldHavePreventedKirkPaid = false

retrospectiveFitCreatesProspectiveCausalProof : Bool
retrospectiveFitCreatesProspectiveCausalProof = false

omittedObservableImpliesSingleCause : Bool
omittedObservableImpliesSingleCause = false

securityToolPresenceImpliesCorrectUse : Bool
securityToolPresenceImpliesCorrectUse = false

correctDetectionImpliesMitigationAdoption : Bool
correctDetectionImpliesMitigationAdoption = false

mitigationAdoptionImpliesHarmPrevention : Bool
mitigationAdoptionImpliesHarmPrevention = false

record KirkVilyaCounterfactualBoundary : Set where
  constructor kirk-vilya-counterfactual-boundary
  field
    eventLayerSeparatelySourced : Bool
    operationalOmissionLayerPaid : Bool
    capabilityClassOverlapPaid : Bool
    causalPreventionPaid : Bool
    eachCounterfactualHopRequiresIdentification : Bool
    conspiracyAttributionCreated : Bool

canonicalKirkVilyaCounterfactualBoundary : KirkVilyaCounterfactualBoundary
canonicalKirkVilyaCounterfactualBoundary =
  kirk-vilya-counterfactual-boundary
    true true true false true false
