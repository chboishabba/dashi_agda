module DASHI.Governance.InstitutionalTechniqueTransferCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

------------------------------------------------------------------------
-- Institutional technique transfer.
--
-- The carrier distinguishes:
--   common ownership
--   shared organisational infrastructure
--   documented transfer of a technique
--   merely analogous use of a technique
--
-- This prevents ownership or visual similarity from being promoted directly
-- into a claim of methodological transfer or hidden common command.
------------------------------------------------------------------------

data InstitutionalDomain : Set where
  tobaccoDomain : InstitutionalDomain
  foodDomain : InstitutionalDomain
  advertisingPRDomain : InstitutionalDomain
  militaryDomain : InstitutionalDomain
  intelligenceDomain : InstitutionalDomain
  policingDomain : InstitutionalDomain
  carceralDomain : InstitutionalDomain
  civicAdministrationDomain : InstitutionalDomain
  healthcareDomain : InstitutionalDomain
  workplaceDomain : InstitutionalDomain
  consumerPlatformDomain : InstitutionalDomain
  politicalCampaignDomain : InstitutionalDomain


data TransferTechnique : Set where
  uncertaintyProduction : TransferTechnique
  populationSegmentation : TransferTechnique
  frontGroupConstruction : TransferTechnique
  behaviouralOptimisation : TransferTechnique
  flavourRewardEngineering : TransferTechnique
  continuousSurveillance : TransferTechnique
  entityResolution : TransferTechnique
  dossierConstruction : TransferTechnique
  riskScoring : TransferTechnique
  relationshipGraphing : TransferTechnique
  interventionPrioritisation : TransferTechnique
  epistemicEnvironmentManagement : TransferTechnique
  complianceOptimisation : TransferTechnique

record InstitutionalSource : Set where
  constructor institutionalSource
  field
    authorInstitution : String
    title : String
    date : String
    identifier : String
    boundedRole : String
    createsTransferConclusion : Bool

open InstitutionalSource public

mkInstitutionalSource : String → String → String → String → String → InstitutionalSource
mkInstitutionalSource a t d i r = institutionalSource a t d i r false

ajphLunchablesPrimarySource : InstitutionalSource
ajphLunchablesPrimarySource =
  mkInstitutionalSource
    "Laura A. Schmidt"
    "Tobacco Industry Contributions to the Development of Ultraprocessed Food in the United States, 1985-2007: A Case Study of Lunchables"
    "2026"
    "American Journal of Public Health 116(7):940-949; DOI 10.2105/AJPH.2026.308491; PMID 42233189"
    "primary internal-document case study: Philip Morris shared proprietary R&D across tobacco and food and applied consumer-driven product-development and better-for-you reformulation approaches to Lunchables"

ucsfLunchablesSource : InstitutionalSource
ucsfLunchablesSource =
  mkInstitutionalSource
    "University of California San Francisco; reporting by Victoria Colliver on Laura Schmidt's archival study"
    "How Big Tobacco Helped Shape the Design of Ultra-Processed Foods"
    "2026-06-03"
    "UCSF News; reports AJPH DOI 10.2105/AJPH.2026.308491"
    "institutional research communication summarising the primary archival study; secondary to the AJPH paper"

mondelezHistorySource : InstitutionalSource
mondelezHistorySource =
  mkInstitutionalSource
    "Mondelez International"
    "Our History"
    "corporate history"
    "General Foods acquired 1985; Kraft acquisition/combination chronology recorded by corporate history"
    "corporate ownership chronology only; does not itself prove research-method transfer"

altriaHeritageSource : InstitutionalSource
altriaHeritageSource =
  mkInstitutionalSource
    "Altria Group"
    "Our Heritage"
    "corporate history"
    "Philip Morris Companies renamed Altria in 2003; Kraft spin-off completed 2007"
    "corporate lineage and divestment chronology only"

record OwnershipRelation : Set where
  constructor ownershipRelation
  field
    parentLabel : String
    subsidiaryLabel : String
    periodLabel : String

record TechniqueTransferWitness : Set where
  constructor techniqueTransferWitness
  field
    sourceDomain : InstitutionalDomain
    targetDomain : InstitutionalDomain
    technique : TransferTechnique
    provenance : List InstitutionalSource
    PersonnelOrDocumentEvidence : Set
    personnelOrDocumentEvidence : PersonnelOrDocumentEvidence

philipMorrisConsumerDevelopmentTransfer : TechniqueTransferWitness
philipMorrisConsumerDevelopmentTransfer =
  techniqueTransferWitness
    tobaccoDomain
    foodDomain
    behaviouralOptimisation
    (ajphLunchablesPrimarySource ∷ ucsfLunchablesSource ∷ [])
    ⊤
    tt

philipMorrisFlavourEngineeringTransfer : TechniqueTransferWitness
philipMorrisFlavourEngineeringTransfer =
  techniqueTransferWitness
    tobaccoDomain
    foodDomain
    flavourRewardEngineering
    (ajphLunchablesPrimarySource ∷ ucsfLunchablesSource ∷ [])
    ⊤
    tt


data OwnershipAloneEstablishesTechniqueTransfer : Set where

ownershipAloneDoesNotEstablishTechniqueTransfer :
  OwnershipAloneEstablishesTechniqueTransfer → ⊥
ownershipAloneDoesNotEstablishTechniqueTransfer ()

------------------------------------------------------------------------
-- Queryable operational person/network grammar.
------------------------------------------------------------------------

record OperationalLegibilitySystem : Set₁ where
  field
    Trace : Set
    Entity : Set
    Relation : Set
    Classification : Set
    Intervention : Set

    resolveEntity : List Trace → Entity
    inferRelations : Entity → List Trace → List Relation
    classify : Entity → List Relation → Classification
    intervene : Entity → Classification → Intervention

record ClosedOperationalLoop
  (S : OperationalLegibilitySystem) : Set₁ where
  field
    traces : List (OperationalLegibilitySystem.Trace S)
    entity : OperationalLegibilitySystem.Entity S
    relations : List (OperationalLegibilitySystem.Relation S)
    classification : OperationalLegibilitySystem.Classification S
    intervention : OperationalLegibilitySystem.Intervention S
    entityResolved : OperationalLegibilitySystem.resolveEntity S traces ≡ entity
    relationsInferred : OperationalLegibilitySystem.inferRelations S entity traces ≡ relations
    classificationProduced : OperationalLegibilitySystem.classify S entity relations ≡ classification
    interventionProduced : OperationalLegibilitySystem.intervene S entity classification ≡ intervention

------------------------------------------------------------------------
-- Prediction versus intervention optimisation.
------------------------------------------------------------------------

record BehaviouralLoop : Set₁ where
  field
    PersonState : Set
    Observation : Set
    Model : Set
    Action : Set

    observe : PersonState → Observation
    infer : Observation → Model
    selectIntervention : Model → Action
    apply : Action → PersonState → PersonState

record InstitutionalTechniqueTransferBoundary : Set where
  constructor institutionalTechniqueTransferBoundary
  field
    commonOwnershipEqualsMethodTransfer : Bool
    analogousTechniqueEqualsCommonCommand : Bool
    militaryOriginMakesCivilUseIllegitimate : Bool
    civilUseMakesMilitaryTechniqueNeutral : Bool
    operationalModelEqualsPerson : Bool
    domainTransferRequiresGovernanceBoundary : Bool
    transferClaimsRequireProvenance : Bool

canonicalInstitutionalTechniqueTransferBoundary : InstitutionalTechniqueTransferBoundary
canonicalInstitutionalTechniqueTransferBoundary =
  institutionalTechniqueTransferBoundary false false false false false true true

record InstitutionalTechniqueTransferReceipt : Set where
  constructor institutionalTechniqueTransferReceipt
  field
    label : String
    scholarlySources : List Sources.ScholarlySource
    institutionalSources : List InstitutionalSource
    boundary : InstitutionalTechniqueTransferBoundary

canonicalInstitutionalTechniqueTransferReceipt : InstitutionalTechniqueTransferReceipt
canonicalInstitutionalTechniqueTransferReceipt =
  institutionalTechniqueTransferReceipt
    "institutional technique transfer: tobacco / military / carceral / commercial / civic"
    (Sources.nationalSmokersAllianceSource
      ∷ Sources.philipMorrisLunchablesPrimary
      ∷ [])
    (ajphLunchablesPrimarySource
      ∷ ucsfLunchablesSource
      ∷ mondelezHistorySource
      ∷ altriaHeritageSource
      ∷ [])
    canonicalInstitutionalTechniqueTransferBoundary
