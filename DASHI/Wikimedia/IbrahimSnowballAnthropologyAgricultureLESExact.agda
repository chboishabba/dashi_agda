module DASHI.Wikimedia.IbrahimSnowballAnthropologyAgricultureLESExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimEnglishAnthropologyHumanityBridgeExact as Anthropology
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES
import DASHI.Environment.PeasantAutonomyAgroecologySourceLineageExact as Peasant
import DASHI.Environment.PluralSustainableLandManagementTraditionsExact as Traditions

------------------------------------------------------------------------
-- IBRAHIM SNOWBALL: ANTHROPOLOGY -> AGRICULTURE/FARMING -> LES
--
-- External navigation/identity observations inspected 2026-09-10:
--   agriculture  Q11451
--   agroecology  Q396338
--   agronomy     Q173113
--
-- Current external descriptions are useful only as navigation coordinates:
-- agriculture/farming is a human practice/economic activity; agroecology is an
-- academic/scientific field spanning ecological processes in agriculture, and
-- current EN also records social/economic/community dimensions.  None of those
-- descriptions determines the DASHI ontology or creates empirical authority.
--
-- Existing repository substrate is already substantial.  Peasant/autonomy
-- agroecology keeps movement self-description, technical agronomy and causal
-- outcome in separate evidence fibres.  LES already proves that management
-- history, ecological relation, knowledge provenance and justice coordinates
-- can remain independently relevant to a planning consumer.
------------------------------------------------------------------------

agricultureQidDemand : Identity.ExternalIdentityDemand
agricultureQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "agriculture/farming identity" "Agriculture"
  Identity.wikidataQid
  (Identity.verified "Q11451" "Wikidata identity checked 2026-09-10")

agroecologyQidDemand : Identity.ExternalIdentityDemand
agroecologyQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "agroecology identity" "Agroecology"
  Identity.wikidataQid
  (Identity.verified "Q396338" "Wikidata identity checked 2026-09-10")

agronomyQidDemand : Identity.ExternalIdentityDemand
agronomyQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "agronomy identity" "Agronomy"
  Identity.wikidataQid
  (Identity.verified "Q173113" "Wikidata identity checked 2026-09-10")

------------------------------------------------------------------------
-- Coverage result: farming/agriculture is not absent.  The surviving debt is
-- a parent/disciplinary bridge from anthropology/humanity into agrarian
-- practice and from there into the existing LES/agroecology fabric without
-- collapsing practice, livelihood, ecology, movement, territory or authority.
------------------------------------------------------------------------

record AgricultureLESCoverageReading : Set where
  constructor agriculture-les-coverage-reading
  field
    agriculturePracticeSubstratePresent : Bool
    sustainableAgricultureSourceRegistryPresent : Bool
    pluralAgrarianTraditionsPresent : Bool
    peasantAutonomyAttributionLanePresent : Bool
    lesSocioEcologicalFabricPresent : Bool
    anthropologyAgrarianParentBridgePresent : Bool
    entirelyNewAgricultureOntologyNeeded : Bool
open AgricultureLESCoverageReading public

currentAgricultureLESCoverage : AgricultureLESCoverageReading
currentAgricultureLESCoverage = agriculture-les-coverage-reading
  true true true true true false false

------------------------------------------------------------------------
-- Snowball witness 1: identical technical farm-practice surface cannot answer
-- whether the same practice is embedded in different livelihood/territorial/
-- governance relations.  This is the anthropology -> farming seam.
------------------------------------------------------------------------

data AgrarianSituatedCase : Set where
  sameTechniqueExternalManagement : AgrarianSituatedCase
  sameTechniqueCommunityTerritorialPractice : AgrarianSituatedCase

data FarmTechniqueSurface : Set where
  sameFarmTechnique : FarmTechniqueSurface

data AgrarianRelationReading : Set where
  technicalManagementOnly : AgrarianRelationReading
  situatedLivelihoodTerritoryRelation : AgrarianRelationReading

projectFarmTechnique : AgrarianSituatedCase → FarmTechniqueSurface
projectFarmTechnique _ = sameFarmTechnique

agrarianRelationReading : AgrarianSituatedCase → AgrarianRelationReading
agrarianRelationReading sameTechniqueExternalManagement = technicalManagementOnly
agrarianRelationReading sameTechniqueCommunityTerritorialPractice = situatedLivelihoodTerritoryRelation

farmTechniqueRelationDefect :
  INF.NonFactorabilityWitness projectFarmTechnique agrarianRelationReading
farmTechniqueRelationDefect = INF.nonFactorabilityWitness
  sameTechniqueExternalManagement
  sameTechniqueCommunityTerritorialPractice
  refl
  (λ ())

farmTechniqueCannotFactorAgrarianRelation :
  INF.FactorsThrough projectFarmTechnique agrarianRelationReading → ⊥
farmTechniqueCannotFactorAgrarianRelation =
  INF.witnessRulesOutEveryFlatFactorisation farmTechniqueRelationDefect

------------------------------------------------------------------------
-- Snowball witness 2: identical present ecological/farm observation cannot
-- determine the relevant management history.  LES already owns the stronger
-- general theorem; this finite agriculture specimen makes the anthropological
-- reading explicit without redefining LES.
------------------------------------------------------------------------

data FarmHistoryCase : Set where
  samePresentFarmShortHistory : FarmHistoryCase
  samePresentFarmLongHistory : FarmHistoryCase

data PresentFarmSurface : Set where
  samePresentFarmObservation : PresentFarmSurface

data FarmHistoryReading : Set where
  shortManagementHistory : FarmHistoryReading
  longManagementHistory : FarmHistoryReading

projectPresentFarm : FarmHistoryCase → PresentFarmSurface
projectPresentFarm _ = samePresentFarmObservation

farmHistoryReading : FarmHistoryCase → FarmHistoryReading
farmHistoryReading samePresentFarmShortHistory = shortManagementHistory
farmHistoryReading samePresentFarmLongHistory = longManagementHistory

presentFarmHistoryDefect :
  INF.NonFactorabilityWitness projectPresentFarm farmHistoryReading
presentFarmHistoryDefect = INF.nonFactorabilityWitness
  samePresentFarmShortHistory samePresentFarmLongHistory refl (λ ())

presentFarmCannotFactorHistory :
  INF.FactorsThrough projectPresentFarm farmHistoryReading → ⊥
presentFarmCannotFactorHistory =
  INF.witnessRulesOutEveryFlatFactorisation presentFarmHistoryDefect

------------------------------------------------------------------------
-- Attribution and Two-Eyed discipline.
--
-- The movement/source lane is not agronomic mechanism evidence; scientific
-- agronomy is not community authority; a community practice is not thereby
-- universal; and a shared ecological observation does not erase knowledge
-- provenance.  Existing owners already carry these boundaries and are reused.
------------------------------------------------------------------------

peasantAttributionBoundary : Peasant.PeasantAutonomyAttributionBoundary
peasantAttributionBoundary = Peasant.canonicalPeasantAutonomyAttributionBoundary

lesBoundary : LES.LESSituatedSocioEcologicalBoundary
lesBoundary = LES.canonicalLESSituatedSocioEcologicalBoundary

anthropologyBoundary : Anthropology.AnthropologyHumanityBoundary
anthropologyBoundary = Anthropology.canonicalAnthropologyHumanityBoundary

record AnthropologyAgricultureLESSnowballBoundary : Set where
  constructor anthropology-agriculture-les-snowball-boundary
  field
    agricultureIdentityRequestedWhenAvailable : Bool
    agroecologyIdentityRequestedWhenAvailable : Bool
    agronomyIdentityRequestedWhenAvailable : Bool
    technicalPracticeEqualsAgrarianSocialRelation : Bool
    scientificAgronomyCreatesCommunityAuthority : Bool
    movementFrameworkProvesAgronomicMechanism : Bool
    oneCommunityPracticeGeneralisesUniversally : Bool
    presentFarmObservationExhaustsManagementHistory : Bool
    twoEyedKnowledgeProvenanceRetained : Bool
    sourceRoleAndClaimOwnerRetained : Bool
    currentAxisVocabularyClaimedComplete : Bool
    anthropologyAgrarianBridgeStillUseful : Bool
open AnthropologyAgricultureLESSnowballBoundary public

canonicalAnthropologyAgricultureLESSnowballBoundary :
  AnthropologyAgricultureLESSnowballBoundary
canonicalAnthropologyAgricultureLESSnowballBoundary =
  anthropology-agriculture-les-snowball-boundary
    true true true
    false false false false false
    true true false true

------------------------------------------------------------------------
-- Explicit WrongType-style firewalls for graph traversal.
------------------------------------------------------------------------

data FarmingTechniqueIsAgrarianMovement : Set where
data AgrarianMovementIsCausalFarmEffect : Set where
data AgriculturalScienceIsAllAgrarianKnowledge : Set where
data LandUseMapCreatesTerritorialAuthority : Set where

farmingTechniqueDoesNotBecomeMovement : FarmingTechniqueIsAgrarianMovement → ⊥
farmingTechniqueDoesNotBecomeMovement ()

movementDoesNotBecomeCausalEffect : AgrarianMovementIsCausalFarmEffect → ⊥
movementDoesNotBecomeCausalEffect ()

agriculturalScienceDoesNotExhaustAgrarianKnowledge :
  AgriculturalScienceIsAllAgrarianKnowledge → ⊥
agriculturalScienceDoesNotExhaustAgrarianKnowledge ()

landUseMapDoesNotCreateTerritorialAuthority : LandUseMapCreatesTerritorialAuthority → ⊥
landUseMapDoesNotCreateTerritorialAuthority ()

-- One repository source anchor retained explicitly so the graph walk does not
-- launder a movement claim into DASHI authorship.
viaCampesinaSourceAnchor : Traditions.TraditionSource
viaCampesinaSourceAnchor = Traditions.viaCampesinaPeasantAgroecology
