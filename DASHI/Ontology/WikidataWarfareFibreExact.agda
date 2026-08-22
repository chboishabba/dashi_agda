module DASHI.Ontology.WikidataWarfareFibreExact where

------------------------------------------------------------------------
-- WIKIDATA WARFARE: CLASS / METACLASS / QUERY GRAPH SPECIMEN
--
-- This module deliberately keeps three questions separate:
--
--   P31 : what kind of CLASS-ITEM is this?
--   P279: what do all instances of this class inherit from?
--   query reachability: what will a P279* consumer actually retrieve?
--
-- That separation is the whole point of the Schemathings warfare example.
-- `type of war` / `type of conflict` are metaclass membership statements.
-- They do not replace P279, and they do not by themselves repair a P279* query.
--
-- Current-item facts below are restricted to the representative statements
-- checked for this specimen. Proposed statements are represented by separate
-- datatypes so a theorem cannot silently rewrite Wikidata.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Finite representative universe.
------------------------------------------------------------------------

data Entity : Set where
  warfare conflict typeOfWar typeOfConflict metaclass typeEntity : Entity
  navalWarfare submarineWarfare economicWarfare : Entity
  mountainWarfare coldWeatherWarfare skiWarfare trenchWarfare : Entity
  staticBattle militaryTactics : Entity
  coldWeather climate weather skiing militarySkier : Entity
  mountainGun mountainArtillery trench : Entity
  alpinistUnit mountainInfantryUnit : Entity
  skiersMilitaryUnit militaryUnitTypeClass mountainUnit militaryUnit : Entity
  alpini : Entity

------------------------------------------------------------------------
-- Property names are first-class only where schema statements talk ABOUT a
-- property. This is not a replacement for the typed relations below.
------------------------------------------------------------------------

data WDProperty : Set where
  p31Prop p279Prop p1963Prop practicedByProp usesProp : WDProperty
  partOfProp facetOfProp hasCauseProp hasEffectProp pointInTimeProp : WDProperty
  handledByProp associatedHazardProp fieldOfWorkProp : WDProperty

------------------------------------------------------------------------
-- Current P31 statements.
------------------------------------------------------------------------

data P31 : Entity → Entity → Set where
  type-of-war-is-metaclass : P31 typeOfWar metaclass
  type-of-conflict-is-metaclass : P31 typeOfConflict metaclass
  naval-is-type-of-war : P31 navalWarfare typeOfWar
  economic-is-type-of-conflict : P31 economicWarfare typeOfConflict
  trench-is-military-tactics : P31 trenchWarfare militaryTactics
  cold-weather-is-climate : P31 coldWeather climate
  alpinist-unit-is-mountain-infantry : P31 alpinistUnit mountainInfantryUnit
  skiers-unit-is-military-unit-type : P31 skiersMilitaryUnit militaryUnitTypeClass

------------------------------------------------------------------------
-- Current P279 statements.
--
-- Note the deliberate contrast:
--   submarine warfare -> naval warfare -> warfare
--   trench warfare -> static battle
--
-- The latter path does not currently reach `warfare` in this specimen.
------------------------------------------------------------------------

data P279 : Entity → Entity → Set where
  naval-sub-warfare : P279 navalWarfare warfare
  submarine-sub-naval : P279 submarineWarfare navalWarfare
  economic-sub-warfare : P279 economicWarfare warfare
  mountain-sub-warfare : P279 mountainWarfare warfare
  cold-weather-warfare-sub-warfare : P279 coldWeatherWarfare warfare
  ski-sub-skiing : P279 skiWarfare skiing
  ski-sub-warfare : P279 skiWarfare warfare
  ski-sub-cold-weather-warfare : P279 skiWarfare coldWeatherWarfare
  ski-sub-mountain-warfare : P279 skiWarfare mountainWarfare
  trench-sub-static-battle : P279 trenchWarfare staticBattle
  cold-weather-sub-weather : P279 coldWeather weather
  skiers-unit-sub-mountain-unit : P279 skiersMilitaryUnit mountainUnit
  skiers-unit-sub-military-unit : P279 skiersMilitaryUnit militaryUnit
  alpini-sub-mountain-infantry : P279 alpini mountainInfantryUnit
  alpini-sub-skiers-unit : P279 alpini skiersMilitaryUnit

------------------------------------------------------------------------
-- Other current relation families. These are not coerced into P279 facets.
------------------------------------------------------------------------

data PracticedBy : Entity → Entity → Set where
  ski-practiced-by-military-skier : PracticedBy skiWarfare militarySkier
  cold-weather-warfare-practiced-by-military-skier :
    PracticedBy coldWeatherWarfare militarySkier


data Uses : Entity → Entity → Set where
  mountain-warfare-uses-mountain-gun : Uses mountainWarfare mountainGun
  mountain-warfare-uses-mountain-artillery : Uses mountainWarfare mountainArtillery
  trench-warfare-uses-trench : Uses trenchWarfare trench


data FieldOfWork : Entity → Entity → Set where
  alpini-field-mountain-warfare : FieldOfWork alpini mountainWarfare

------------------------------------------------------------------------
-- Native schema documentation already demonstrated by `type of conflict`.
-- P1963 is advisory/property-shape information, not a hard logical constraint.
------------------------------------------------------------------------

data P1963 : Entity → WDProperty → Set where
  conflict-shape-part-of : P1963 typeOfConflict partOfProp
  conflict-shape-facet-of : P1963 typeOfConflict facetOfProp
  conflict-shape-has-cause : P1963 typeOfConflict hasCauseProp
  conflict-shape-has-effect : P1963 typeOfConflict hasEffectProp
  conflict-shape-point-in-time : P1963 typeOfConflict pointInTimeProp
  conflict-shape-handled-by : P1963 typeOfConflict handledByProp
  conflict-shape-associated-hazard : P1963 typeOfConflict associatedHazardProp

------------------------------------------------------------------------
-- Candidate metaclass additions are stated separately from current Wikidata.
-- Populating the metaclass helps enumerate/check the intended population, but
-- does NOT itself make a class reachable through P279*.
------------------------------------------------------------------------

data ProposedTypeOfWar : Entity → Set where
  submarine-is-war-type : ProposedTypeOfWar submarineWarfare
  mountain-is-war-type : ProposedTypeOfWar mountainWarfare
  cold-weather-is-war-type : ProposedTypeOfWar coldWeatherWarfare
  ski-is-war-type : ProposedTypeOfWar skiWarfare
  trench-is-war-type : ProposedTypeOfWar trenchWarfare

------------------------------------------------------------------------
-- Proposed structural repair for trench warfare.
--
-- Keep the current static-battle classification and add a second superclass
-- only if community consensus accepts that every instance of trench warfare is
-- also warfare. Multiple inheritance is the Wikidata-native expression of the
-- two simultaneously true class relationships.
------------------------------------------------------------------------

data ProposedP279 : Entity → Entity → Set where
  trench-sub-warfare : ProposedP279 trenchWarfare warfare

------------------------------------------------------------------------
-- P279 reflexive/transitive closure: this is the semantic core of the SPARQL
-- path `wdt:P279*` used by the film query.
------------------------------------------------------------------------

data P279Star : Entity → Entity → Set where
  star-refl : ∀ {x} → P279Star x x
  star-step : ∀ {x y z} → P279 x y → P279Star y z → P279Star x z

naval-under-warfare : P279Star navalWarfare warfare
naval-under-warfare = star-step naval-sub-warfare star-refl

submarine-under-naval : P279Star submarineWarfare navalWarfare
submarine-under-naval = star-step submarine-sub-naval star-refl

submarine-under-warfare : P279Star submarineWarfare warfare
submarine-under-warfare =
  star-step submarine-sub-naval
    (star-step naval-sub-warfare star-refl)

economic-under-warfare : P279Star economicWarfare warfare
economic-under-warfare = star-step economic-sub-warfare star-refl

mountain-under-warfare : P279Star mountainWarfare warfare
mountain-under-warfare = star-step mountain-sub-warfare star-refl

cold-weather-under-warfare : P279Star coldWeatherWarfare warfare
cold-weather-under-warfare =
  star-step cold-weather-warfare-sub-warfare star-refl

ski-under-mountain : P279Star skiWarfare mountainWarfare
ski-under-mountain = star-step ski-sub-mountain-warfare star-refl

ski-under-cold-weather : P279Star skiWarfare coldWeatherWarfare
ski-under-cold-weather = star-step ski-sub-cold-weather-warfare star-refl

ski-under-warfare : P279Star skiWarfare warfare
ski-under-warfare = star-step ski-sub-warfare star-refl

trench-under-static-battle : P279Star trenchWarfare staticBattle
trench-under-static-battle = star-step trench-sub-static-battle star-refl

------------------------------------------------------------------------
-- Finite observation matching the representative current P279 graph.
--
-- This Bool is NOT the ontology. It is the exact observation made by the
-- consumer question "does the current P279* graph reach warfare?" on this
-- finite specimen. It exists so we can prove query failure constructively.
------------------------------------------------------------------------

underWarfare : Entity → Bool
underWarfare warfare = true
underWarfare navalWarfare = true
underWarfare submarineWarfare = true
underWarfare economicWarfare = true
underWarfare mountainWarfare = true
underWarfare coldWeatherWarfare = true
underWarfare skiWarfare = true
underWarfare trenchWarfare = false
underWarfare _ = false

submarineRetrievedAsWarfare : underWarfare submarineWarfare ≡ true
submarineRetrievedAsWarfare = refl

trenchMissedByCurrentWarfareProjection : underWarfare trenchWarfare ≡ false
trenchMissedByCurrentWarfareProjection = refl

------------------------------------------------------------------------
-- Positive multi-inheritance specimen.
------------------------------------------------------------------------

record SkiWarfareShape : Set where
  constructor skiWarfareShape
  field
    isSkiing : P279 skiWarfare skiing
    isWarfare : P279 skiWarfare warfare
    isColdWeatherWarfare : P279 skiWarfare coldWeatherWarfare
    isMountainWarfare : P279 skiWarfare mountainWarfare
    practitioner : PracticedBy skiWarfare militarySkier

canonicalSkiWarfareShape : SkiWarfareShape
canonicalSkiWarfareShape =
  skiWarfareShape
    ski-sub-skiing
    ski-sub-warfare
    ski-sub-cold-weather-warfare
    ski-sub-mountain-warfare
    ski-practiced-by-military-skier

------------------------------------------------------------------------
-- Object-level separation: warfare classes and military units are not one
-- carrier merely because their labels share military vocabulary.
------------------------------------------------------------------------

alpinistUnitIsUnitTyped : P31 alpinistUnit mountainInfantryUnit
alpinistUnitIsUnitTyped = alpinist-unit-is-mountain-infantry

alpiniLinksUnitStructureBackToWarfareField :
  P279 alpini mountainInfantryUnit ×
  P279 alpini skiersMilitaryUnit ×
  FieldOfWork alpini mountainWarfare
alpiniLinksUnitStructureBackToWarfareField =
  alpini-sub-mountain-infantry ,
  alpini-sub-skiers-unit ,
  alpini-field-mountain-warfare

------------------------------------------------------------------------
-- Query-oriented conformance is intentionally narrower than "all members of
-- type of war". For the declared warfare-film consumer, a class is conformant
-- only when it both belongs to the selected metaclass population and has an
-- actual P279* path into warfare.
------------------------------------------------------------------------

record WarfareQueryConforms (x : Entity) : Set where
  constructor warfareQueryConforms
  field
    typed : ProposedTypeOfWar x
    underWarfarePath : P279Star x warfare

submarineConforms : WarfareQueryConforms submarineWarfare
submarineConforms =
  warfareQueryConforms submarine-is-war-type submarine-under-warfare

mountainConforms : WarfareQueryConforms mountainWarfare
mountainConforms =
  warfareQueryConforms mountain-is-war-type mountain-under-warfare

skiConforms : WarfareQueryConforms skiWarfare
skiConforms = warfareQueryConforms ski-is-war-type ski-under-warfare

coldWeatherWarfareConforms : WarfareQueryConforms coldWeatherWarfare
coldWeatherWarfareConforms =
  warfareQueryConforms cold-weather-is-war-type cold-weather-under-warfare

------------------------------------------------------------------------
-- Boundary claims.
------------------------------------------------------------------------

record WarfareOntologyBoundary : Set where
  constructor warfareOntologyBoundary
  field
    p31ReplacesP279Inheritance : Bool
    metaclassTypingRepairsP279ReachabilityByItself : Bool
    flatDirectChildrenAreAutomaticallyWrong : Bool
    multipleInheritanceIsAllowedWhenBothClassClaimsHold : Bool
    trenchCurrentP279PathReachesWarfare : Bool
    syntheticFacetVocabularyRequired : Bool
    warfareClassesAndConcreteMilitaryUnitsAreSameLevel : Bool

canonicalWarfareOntologyBoundary : WarfareOntologyBoundary
canonicalWarfareOntologyBoundary =
  warfareOntologyBoundary false false false true false false false
