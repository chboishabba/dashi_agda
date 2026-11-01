module DASHI.Wikimedia.IbrahimSnowballGeographyPlaceTerritoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimCountryCommunityKnowledgeAuthorityBridgeExact as CountryBridge
import DASHI.Wikimedia.IbrahimSnowballStateAnthropologyArchaeologyExact as Prior

------------------------------------------------------------------------
-- IBRAHIM SNOWBALL FRONTIER: GEOGRAPHY / PLACE / TERRITORY
--
-- Current EN/Wikidata observations inspected 2026-09-10:
--   Geography           Q1071
--   Human geography     Q12831143
--   Political geography Q191320
--
-- Current EN describes geography as a bridge between natural and social
-- science, with space/place/time/scale as recurring core concepts. Human
-- geography studies people-place relations; political geography studies the
-- spatially uneven outcomes/structures of political processes.
--
-- These are external navigation and identity coordinates only.  They do not
-- turn metric position into place meaning, mapped territory into political or
-- Country authority, or a map/database into exhaustive situated knowledge.
------------------------------------------------------------------------

geographyQidDemand : Identity.ExternalIdentityDemand
geographyQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "geography identity" "Geography"
  Identity.wikidataQid
  (Identity.verified "Q1071" "Wikidata identity checked 2026-09-10")

humanGeographyQidDemand : Identity.ExternalIdentityDemand
humanGeographyQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "human geography identity" "Human geography"
  Identity.wikidataQid
  (Identity.verified "Q12831143" "Wikidata identity checked 2026-09-10")

politicalGeographyQidDemand : Identity.ExternalIdentityDemand
politicalGeographyQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "political geography identity" "Political geography"
  Identity.wikidataQid
  (Identity.verified "Q191320" "Wikidata identity checked 2026-09-10")

------------------------------------------------------------------------
-- Coverage audit: substantial substrate, missing canonical discipline parent.
------------------------------------------------------------------------

record GeographyCoverageReading : Set where
  constructor geography-coverage-reading
  field
    canonicalGeographyOwnerObserved : Bool
    physicalEnvironmentalSubstratePresent : Bool
    humanSocialSpatialSubstratePresent : Bool
    countryPlaceSubstratePresent : Bool
    politicalGeographySourceLanePresent : Bool
    technicalSpatialToolingPresent : Bool
    geographyEntirelyMissing : Bool
    parentConsolidationDebt : Bool
open GeographyCoverageReading public

currentGeographyCoverage : GeographyCoverageReading
currentGeographyCoverage = geography-coverage-reading
  false true true true true true false true

------------------------------------------------------------------------
-- Snowball witness 1: coordinate equality cannot determine situated place.
------------------------------------------------------------------------

data PlaceSituatedCase : Set where
  sameCoordinateExternalLocationOnly : PlaceSituatedCase
  sameCoordinateSituatedCountryRelation : PlaceSituatedCase

data CoordinateSurface : Set where
  sameMappedCoordinate : CoordinateSurface

data PlaceReading : Set where
  locationWithoutSituatedAuthority : PlaceReading
  situatedCountryPlaceRelation : PlaceReading

projectCoordinate : PlaceSituatedCase → CoordinateSurface
projectCoordinate _ = sameMappedCoordinate

placeReading : PlaceSituatedCase → PlaceReading
placeReading sameCoordinateExternalLocationOnly = locationWithoutSituatedAuthority
placeReading sameCoordinateSituatedCountryRelation = situatedCountryPlaceRelation

coordinatePlaceDefect : INF.NonFactorabilityWitness projectCoordinate placeReading
coordinatePlaceDefect = INF.nonFactorabilityWitness
  sameCoordinateExternalLocationOnly
  sameCoordinateSituatedCountryRelation
  refl
  (λ ())

coordinateCannotFactorSituatedPlace :
  INF.FactorsThrough projectCoordinate placeReading → ⊥
coordinateCannotFactorSituatedPlace =
  INF.witnessRulesOutEveryFlatFactorisation coordinatePlaceDefect

------------------------------------------------------------------------
-- Snowball witness 2: identical territorial outline cannot determine the
-- authority/recognition relation carried by a polity or Country.
------------------------------------------------------------------------

data TerritorySituatedCase : Set where
  sameTerritoryStateAdministrativeClaim : TerritorySituatedCase
  sameTerritoryPreExistingCommunityAuthority : TerritorySituatedCase

data TerritorySurface : Set where
  sameMappedTerritory : TerritorySurface

data TerritoryAuthorityReading : Set where
  stateAdministrativeAuthorityReading : TerritoryAuthorityReading
  preExistingCommunityAuthorityReading : TerritoryAuthorityReading

projectTerritory : TerritorySituatedCase → TerritorySurface
projectTerritory _ = sameMappedTerritory

territoryAuthorityReading : TerritorySituatedCase → TerritoryAuthorityReading
territoryAuthorityReading sameTerritoryStateAdministrativeClaim =
  stateAdministrativeAuthorityReading
territoryAuthorityReading sameTerritoryPreExistingCommunityAuthority =
  preExistingCommunityAuthorityReading

territoryAuthorityDefect :
  INF.NonFactorabilityWitness projectTerritory territoryAuthorityReading
territoryAuthorityDefect = INF.nonFactorabilityWitness
  sameTerritoryStateAdministrativeClaim
  sameTerritoryPreExistingCommunityAuthority
  refl
  (λ ())

territoryCannotFactorAuthority :
  INF.FactorsThrough projectTerritory territoryAuthorityReading → ⊥
territoryCannotFactorAuthority =
  INF.witnessRulesOutEveryFlatFactorisation territoryAuthorityDefect

------------------------------------------------------------------------
-- Two-Eyed/snowball reading.
--
-- Physical/spatial and situated/social/Country observations may be coordinated
-- without being fused.  Which axes survive is consumer-relative; the finite
-- examples below are discoveries, not a universal geography ontology.
------------------------------------------------------------------------

record GeographySnowballBoundary : Set where
  constructor geography-snowball-boundary
  field
    geographyBridgesNaturalAndSocialSearch : Bool
    spatialCoordinateEqualsPlaceMeaning : Bool
    mappedTerritoryEqualsAuthority : Bool
    physicalGeographyExhaustsGeography : Bool
    humanGeographyExhaustsCountryKnowledge : Bool
    twoEyedCoordinationRequiresFusion : Bool
    attributionAndQidsRetainedWhenRelevant : Bool
    currentAxisVocabularyClaimedComplete : Bool
    canonicalParentStillUseful : Bool
open GeographySnowballBoundary public

canonicalGeographySnowballBoundary : GeographySnowballBoundary
canonicalGeographySnowballBoundary = geography-snowball-boundary
  true false false false false false true false true

countryAuthorityPrior : CountryBridge.CountryCommunityKnowledgeAuthorityBridgeReceipt
countryAuthorityPrior = CountryBridge.canonicalCountryCommunityKnowledgeAuthorityBridgeReceipt

priorGraphBoundary : Prior.StateAnthropologyArchaeologySnowballBoundary
priorGraphBoundary = Prior.canonicalStateAnthropologyArchaeologySnowballBoundary
