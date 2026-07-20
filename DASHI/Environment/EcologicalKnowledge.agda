module DASHI.Environment.EcologicalKnowledge where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Environment.EcologicalEvidenceGates as Evidence
import DASHI.Environment.FunctionalEcology as Eco

------------------------------------------------------------------------
-- Versioned, regional ecological knowledge records.

data KnowledgeKind : Set where
  functionalTrait : KnowledgeKind
  hostMycorrhizaCompatibility : KnowledgeKind
  floweringCalendar : KnowledgeKind
  pollinatorRange : KnowledgeKind
  pollinatorCompetition : KnowledgeKind
  threatenedHabitatRequirement : KnowledgeKind
  cropSuitability : KnowledgeKind
  grazingTolerance : KnowledgeKind
  remediationTrait : KnowledgeKind
  environmentalEnvelope : KnowledgeKind
  invasiveRisk : KnowledgeKind
  biosecurityRisk : KnowledgeKind

record RegionContext : Set where
  constructor mkRegionContext
  field
    regionName : String
    jurisdiction : String
    climateClassification : String
    soilClassification : String
    bioregion : String
    custodiansOrCommunities : List String
open RegionContext public

record KnowledgeEntry : Set where
  constructor mkKnowledgeEntry
  field
    entryId : String
    kind : KnowledgeKind
    subject : String
    functionalGroups : List Eco.FunctionalGroup
    region : RegionContext
    evidence : List Evidence.EvidenceSource
    validFrom : String
    reviewedAt : String
    version : String
    confidenceDepth : Nat
    limitations : List String
    active : Bool
open KnowledgeEntry public

record KnowledgeCatalogue : Set where
  constructor mkKnowledgeCatalogue
  field
    catalogueName : String
    catalogueVersion : String
    entries : List KnowledgeEntry
    schemaReference : String
    provenanceManifest : List String
    regionalFallbackPolicy : String
    updatePolicy : String
open KnowledgeCatalogue public

record KnowledgeQuery : Set where
  constructor mkKnowledgeQuery
  field
    requestedKind : KnowledgeKind
    targetRegion : RegionContext
    subjectFilter : String
    intendedUse : String
    minimumConfidenceDepth : Nat
open KnowledgeQuery public

record KnowledgeResult : Set where
  constructor mkKnowledgeResult
  field
    query : KnowledgeQuery
    matchingEntries : List KnowledgeEntry
    exactRegionalMatch : Bool
    transferEvidenceRequired : Bool
    missingDataDisclosed : List String
    humanReviewRequired : Bool
open KnowledgeResult public

record KnowledgeBoundary : Set where
  constructor mkKnowledgeBoundary
  field
    catalogueEntryIsNotTimelessFact : Bool
    regionalTransferMustBeExplicit : Bool
    absenceOfEntryIsNotEvidenceOfAbsence : Bool
    communityKnowledgeNeedsConsentAndAttribution : Bool
    legalStatusRequiresCurrentAuthority : Bool
    recommendationsRequireEvidenceGates : Bool
open KnowledgeBoundary public

canonicalKnowledgeBoundary : KnowledgeBoundary
canonicalKnowledgeBoundary =
  mkKnowledgeBoundary true true true true true true
