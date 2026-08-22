module DASHI.Ontology.WikidataWarfareFibreExact where

------------------------------------------------------------------------
-- WIKIDATA WARFARE: CURRENT GRAPH, NORMALISED FACETS, AND FIBRE DEFECTS
--
-- Finite specimen reconstructed from live Wikidata items on 2026-08-22.
-- This module deliberately separates:
--
--   1. current Wikidata assertions (P31 / P279 / auxiliary properties),
--   2. query observations induced by the current graph, and
--   3. a normalised semantic facet layer proposed for consumer queries.
--
-- The normalised layer is NOT asserted to be current Wikidata truth.  It is a
-- typed target vocabulary extracted from the distinctions the items themselves
-- are trying to express.  In particular, P31 is not identified with "facet":
-- P31 classifies the class item; P279 carries subclass inheritance; semantic
-- dimensions such as operational domain, environment, tactic, mechanism and
-- platform are separate coordinates.
--
-- Live calibration used for the central examples:
--   Q876274  naval warfare:
--     P31 Q124867660 (type of war)
--     P279 Q12786121 (warfare), conflict
--   Q2296073 economic warfare:
--     P31 Q125092269 (type of conflict)
--     P279 Q12786121 (warfare)
--     facet of national economic security
--   Q124867660 type of war:
--     Wikidata metaclass for war and warfare; applies to type of conflict.
--   Q125092269 type of conflict:
--     Wikidata metaclass for conflicts.
--
-- Wikidata's data model identifies P31 with rdf:type and P279 with
-- rdfs:subClassOf.  The finite proofs below therefore never replace one with
-- the other merely because both can read as "kind of" in English.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Objects in the finite warfare specimen.
------------------------------------------------------------------------

data Entity : Set where
  warfare conflict typeOfWar typeOfConflict militaryTactics staticBattle : Entity
  navalWarfare submarineWarfare economicWarfare mountainWarfare : Entity
  trenchWarfare skiWarfare coldWeatherWarfare unrestrictedSubmarineWarfare : Entity
  skiing nationalEconomicSecurity mountainGun mountainArtillery trench : Entity
  militarySkier submarine worldWarI : Entity

------------------------------------------------------------------------
-- Current Wikidata relation families.
-- Keeping these as different types blocks accidental P31/P279 conflation.
------------------------------------------------------------------------

data P31 : Entity → Entity → Set where
  naval-is-type-of-war : P31 navalWarfare typeOfWar
  economic-is-type-of-conflict : P31 economicWarfare typeOfConflict
  trench-is-military-tactics : P31 trenchWarfare militaryTactics


data P279 : Entity → Entity → Set where
  warfare-sub-conflict : P279 warfare conflict
  naval-sub-warfare : P279 navalWarfare warfare
  naval-sub-conflict : P279 navalWarfare conflict
  submarine-sub-naval : P279 submarineWarfare navalWarfare
  economic-sub-warfare : P279 economicWarfare warfare
  mountain-sub-warfare : P279 mountainWarfare warfare
  trench-sub-static-battle : P279 trenchWarfare staticBattle
  ski-sub-skiing : P279 skiWarfare skiing
  ski-sub-warfare : P279 skiWarfare warfare
  ski-sub-cold-weather : P279 skiWarfare coldWeatherWarfare
  ski-sub-mountain : P279 skiWarfare mountainWarfare
  unrestricted-sub-warfare : P279 unrestrictedSubmarineWarfare warfare
  unrestricted-sub-submarine : P279 unrestrictedSubmarineWarfare submarineWarfare


data AuxProperty : Set where
  facetOf uses partOf practicedBy hasCharacteristic participatedIn : AuxProperty


data Aux : Entity → AuxProperty → Entity → Set where
  economic-facet-national-security : Aux economicWarfare facetOf nationalEconomicSecurity
  mountain-uses-gun : Aux mountainWarfare uses mountainGun
  mountain-uses-artillery : Aux mountainWarfare uses mountainArtillery
  trench-uses-trench : Aux trenchWarfare uses trench
  submarine-part-naval : Aux submarineWarfare partOf navalWarfare
  ski-practiced-by-military-skier : Aux skiWarfare practicedBy militarySkier
  unrestricted-characteristic-submarine : Aux unrestrictedSubmarineWarfare hasCharacteristic submarine
  unrestricted-participated-wwi : Aux unrestrictedSubmarineWarfare participatedIn worldWarI

------------------------------------------------------------------------
-- Immediate sanity theorem: the economic case has BOTH metaclass membership
-- and subclass inheritance.  These statements are complementary, not rivals.
------------------------------------------------------------------------

economicP31TypeOfConflict : P31 economicWarfare typeOfConflict
economicP31TypeOfConflict = economic-is-type-of-conflict

economicP279Warfare : P279 economicWarfare warfare
economicP279Warfare = economic-sub-warfare

navalP31TypeOfWar : P31 navalWarfare typeOfWar
navalP31TypeOfWar = naval-is-type-of-war

navalP279Warfare : P279 navalWarfare warfare
navalP279Warfare = naval-sub-warfare

------------------------------------------------------------------------
-- Closed P279 reachability for the specimen.
------------------------------------------------------------------------

data P279Star : Entity → Entity → Set where
  star-refl : ∀ {x} → P279Star x x
  star-step : ∀ {x y z} → P279 x y → P279Star y z → P279Star x z

submarine-under-naval : P279Star submarineWarfare navalWarfare
submarine-under-naval = star-step submarine-sub-naval star-refl

submarine-under-warfare : P279Star submarineWarfare warfare
submarine-under-warfare =
  star-step submarine-sub-naval (star-step naval-sub-warfare star-refl)

unrestricted-under-naval : P279Star unrestrictedSubmarineWarfare navalWarfare
unrestricted-under-naval =
  star-step unrestricted-sub-submarine
    (star-step submarine-sub-naval star-refl)

------------------------------------------------------------------------
-- Finite query observations.  These are deliberately consumer surfaces, not
-- claims that Boolean classification reconstructs the underlying graph.
------------------------------------------------------------------------

data P31Observation : Set where
  noRecordedP31 typeWarObs typeConflictObs militaryTacticsObs : P31Observation

p31Observation : Entity → P31Observation
p31Observation navalWarfare = typeWarObs
p31Observation economicWarfare = typeConflictObs
p31Observation trenchWarfare = militaryTacticsObs
p31Observation _ = noRecordedP31

underWarfare : Entity → Bool
underWarfare warfare = true
underWarfare navalWarfare = true
underWarfare submarineWarfare = true
underWarfare economicWarfare = true
underWarfare mountainWarfare = true
underWarfare skiWarfare = true
underWarfare unrestrictedSubmarineWarfare = true
underWarfare _ = false

underNaval : Entity → Bool
underNaval navalWarfare = true
underNaval submarineWarfare = true
underNaval unrestrictedSubmarineWarfare = true
underNaval _ = false

------------------------------------------------------------------------
-- Exact collision witnesses.
--
-- P31 alone cannot support the naval consumer: submarine and mountain warfare
-- have the same current P31 observation but different naval membership.
------------------------------------------------------------------------

p31SubmarineMountainCollision :
  p31Observation submarineWarfare ≡ p31Observation mountainWarfare
p31SubmarineMountainCollision = refl

navalConsumerSeparatesSubmarineMountain :
  underNaval submarineWarfare ≡ true
navalConsumerSeparatesSubmarineMountain = refl

mountainIsNotNavalInSpecimen :
  underNaval mountainWarfare ≡ false
mountainIsNotNavalInSpecimen = refl

-- Even adding the one-bit "under warfare" projection does not repair that
-- collision: both are warfare descendants, but only one is naval.

submarineUnderWarfareObserved : underWarfare submarineWarfare ≡ true
submarineUnderWarfareObserved = refl

mountainUnderWarfareObserved : underWarfare mountainWarfare ≡ true
mountainUnderWarfareObserved = refl

------------------------------------------------------------------------
-- Trench warfare is the recall defect for the bare P279* warfare query in the
-- reconstructed specimen: its recorded parent is static battle, not warfare.
------------------------------------------------------------------------

trenchMissedByCurrentWarfareProjection : underWarfare trenchWarfare ≡ false
trenchMissedByCurrentWarfareProjection = refl

------------------------------------------------------------------------
-- Normalised semantic target.
--
-- This is the object/relation family we actually want for faceted consumers.
-- It is orthogonal to P31/P279: an item may retain its current metaclass and
-- inheritance statements while also carrying several typed semantic facets.
------------------------------------------------------------------------

data FacetAxis : Set where
  operationalDomain environment tacticDoctrine mechanism platform mobility : FacetAxis


data FacetValue : FacetAxis → Set where
  navalDomain : FacetValue operationalDomain
  mountainEnvironment coldEnvironment : FacetValue environment
  trenchTactic unrestrictedDoctrine : FacetValue tacticDoctrine
  economicMechanism : FacetValue mechanism
  submarinePlatform : FacetValue platform
  skiMobility : FacetValue mobility


data HasFacet : (x : Entity) → (axis : FacetAxis) → FacetValue axis → Set where
  naval-domain : HasFacet navalWarfare operationalDomain navalDomain
  submarine-naval-domain : HasFacet submarineWarfare operationalDomain navalDomain
  unrestricted-naval-domain : HasFacet unrestrictedSubmarineWarfare operationalDomain navalDomain

  mountain-environment : HasFacet mountainWarfare environment mountainEnvironment
  ski-mountain-environment : HasFacet skiWarfare environment mountainEnvironment
  ski-cold-environment : HasFacet skiWarfare environment coldEnvironment

  trench-tactic : HasFacet trenchWarfare tacticDoctrine trenchTactic
  unrestricted-doctrine : HasFacet unrestrictedSubmarineWarfare tacticDoctrine unrestrictedDoctrine

  economic-mechanism : HasFacet economicWarfare mechanism economicMechanism

  submarine-platform : HasFacet submarineWarfare platform submarinePlatform
  unrestricted-submarine-platform : HasFacet unrestrictedSubmarineWarfare platform submarinePlatform

  ski-mobility : HasFacet skiWarfare mobility skiMobility

------------------------------------------------------------------------
-- Core separation results.
------------------------------------------------------------------------

-- Mountain and economic warfare may legitimately remain P279 siblings under
-- warfare while being separated on typed semantic axes.

mountainAndEconomicShareCurrentParent :
  P279 mountainWarfare warfare × P279 economicWarfare warfare
mountainAndEconomicShareCurrentParent = mountain-sub-warfare , economic-sub-warfare
  where
  open import Data.Product using (_×_; _,_)

mountainCarriesEnvironmentFacet :
  HasFacet mountainWarfare environment mountainEnvironment
mountainCarriesEnvironmentFacet = mountain-environment

economicCarriesMechanismFacet :
  HasFacet economicWarfare mechanism economicMechanism
economicCarriesMechanismFacet = economic-mechanism

-- Submarine warfare demonstrates inheritance plus a richer facet profile:
-- naval domain is inherited/normalised as a query facet while submarine is a
-- platform facet.  Neither statement requires replacing P279 with P31.

submarineCarriesNavalDomain :
  HasFacet submarineWarfare operationalDomain navalDomain
submarineCarriesNavalDomain = submarine-naval-domain

submarineCarriesPlatform :
  HasFacet submarineWarfare platform submarinePlatform
submarineCarriesPlatform = submarine-platform

-- Ski warfare demonstrates genuine multi-axis membership.

skiCarriesTerrainClimateAndMobility :
  HasFacet skiWarfare environment mountainEnvironment ×
  HasFacet skiWarfare environment coldEnvironment ×
  HasFacet skiWarfare mobility skiMobility
skiCarriesTerrainClimateAndMobility =
  ski-mountain-environment , ski-cold-environment , ski-mobility
  where
  open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Consumer-level normal form.
--
-- A useful warfare query should state which relation it consumes:
--   * hierarchy consumer: P279Star
--   * metaclass consumer: P31
--   * facet consumer: HasFacet
-- rather than assuming a single property tree answers all three questions.
------------------------------------------------------------------------

record WarfareQueryInterface : Set₁ where
  field
    Class : Set
    Meta : Class → Entity → Set
    Subclass : Class → Entity → Set
    Facet : (Class → FacetAxis → Set)

record WarfareOntologyBoundary : Set where
  constructor warfareOntologyBoundary
  field
    p31EqualsP279 : Bool
    p31IsSemanticFacetAxis : Bool
    p279AloneSeparatesAllWarfareFacets : Bool
    semanticFacetsMayCoexistWithP31AndP279 : Bool
    flatSiblingsMayDifferOnTypedFacets : Bool

canonicalWarfareOntologyBoundary : WarfareOntologyBoundary
canonicalWarfareOntologyBoundary =
  warfareOntologyBoundary false false false true true
