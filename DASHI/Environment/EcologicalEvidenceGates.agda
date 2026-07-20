module DASHI.Environment.EcologicalEvidenceGates where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Environment.FunctionalEcology as Eco

------------------------------------------------------------------------
-- Evidence-bearing ecological recommendation gates.

record EvidenceSource : Set where
  constructor mkEvidenceSource
  field
    citationOrDataset : String
    version : String
    geographicScope : String
    temporalScope : String
    methodSummary : String
    confidenceDepth : Nat
    independentlyReviewed : Bool
open EvidenceSource public

record EnvironmentalRange : Set where
  constructor mkEnvironmentalRange
  field
    variableName : String
    unit : String
    lowerBound : Nat
    upperBound : Nat
    observedValue : Nat
    withinDeclaredRange : Bool
    source : EvidenceSource
open EnvironmentalRange public

record HostCompatibilityWitness : Set where
  constructor mkHostCompatibilityWitness
  field
    fungalGuild : Eco.FungalGuild
    hostGroup : Eco.FunctionalGroup
    compatibilitySource : EvidenceSource
    hostEvidence : String
    incompatibleHostsExcluded : List String
    locallyApplicable : Bool
open HostCompatibilityWitness public

record BiogeographicStatus : Set where
  constructor mkBiogeographicStatus
  field
    taxonOrInoculant : String
    nativeStatus : String
    jurisdiction : String
    evidence : EvidenceSource
    introductionRiskReviewed : Bool
open BiogeographicStatus public

record PathogenRiskWitness : Set where
  constructor mkPathogenRiskWitness
  field
    candidateName : String
    screenedPathogens : List String
    screeningMethod : String
    laboratoryOrRegulatorReference : String
    residualRisk : String
    riskAcceptedByAuthority : Bool
open PathogenRiskWitness public

record InoculantProvenanceWitness : Set where
  constructor mkInoculantProvenanceWitness
  field
    supplierOrCollection : String
    batchIdentifier : String
    chainOfCustody : List String
    storageConditions : String
    expiryOrViabilityReference : String
    provenanceAuditable : Bool
open InoculantProvenanceWitness public

record RegulatoryWitness : Set where
  constructor mkRegulatoryWitness
  field
    jurisdiction : String
    permitOrRule : String
    authorityReference : String
    currentlyValid : Bool
    useConditions : List String
open RegulatoryWitness public

record GeographicTransferWitness : Set where
  constructor mkGeographicTransferWitness
  field
    sourceRegion : String
    targetRegion : String
    climateAnalogueEvidence : EvidenceSource
    soilAnalogueEvidence : EvidenceSource
    transferLimitations : List String
    transferAccepted : Bool
open GeographicTransferWitness public

record MycorrhizalRecommendationEvidence : Set where
  constructor mkMycorrhizalRecommendationEvidence
  field
    candidate : Eco.MycorrhizalCandidate
    hostCompatibility : List HostCompatibilityWitness
    soilPH : EnvironmentalRange
    soilMoisture : EnvironmentalRange
    biogeographicStatus : BiogeographicStatus
    pathogenRisk : PathogenRiskWitness
    provenance : InoculantProvenanceWitness
    regulation : RegulatoryWitness
    transfer : GeographicTransferWitness
    fieldTrialOrLocalObservation : EvidenceSource
    allEvidenceReviewed : Bool
open MycorrhizalRecommendationEvidence public

record SpeciesPlanningEvidence : Set where
  constructor mkSpeciesPlanningEvidence
  field
    species : Eco.SpeciesRefinement
    habitatSources : List EvidenceSource
    threatSources : List EvidenceSource
    seasonalEvidence : List EvidenceSource
    connectivityEvidence : List EvidenceSource
    noNetHarmAssessment : String
    localExpertReview : Bool
    communityOrCustodianReview : Bool
open SpeciesPlanningEvidence public

record EvidenceGateBoundary : Set where
  constructor mkEvidenceGateBoundary
  field
    categoryMembershipIsNotRecommendation : Bool
    compatibilityRequiresSource : Bool
    localTransferMustBeJustified : Bool
    biosecurityCannotBeInferredFromBenefit : Bool
    regulationCannotBeInferredFromEcology : Bool
    threatenedSpeciesUseRequiresLocalReview : Bool
open EvidenceGateBoundary public

canonicalEvidenceGateBoundary : EvidenceGateBoundary
canonicalEvidenceGateBoundary =
  mkEvidenceGateBoundary true true true true true true
