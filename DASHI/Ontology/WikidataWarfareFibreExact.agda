module DASHI.Ontology.WikidataWarfareFibreExact where

------------------------------------------------------------------------
-- WIKIDATA WARFARE: NATIVE METACLASS / PROPERTY-SHAPE MODEL
--
-- Reconstructed from live Wikidata on 2026-08-22.
--
-- Crucial correction: do NOT invent environment/mechanism/platform facets.
-- Keep actual Wikidata objects and actual relation families.  Use P1963
-- (properties for this type) as the schema-level mechanism: when a metaclass is
-- used as the object of P31, P1963 records the properties normally applicable
-- to its instances.  Hard conformance is a separate proof obligation.
--
-- Q1210930 is mountain warfare; "Alpine warfare" is an alias of that SAME item.
-- Q1558613 is instead a concrete IDF Alpinist Unit, currently typed as a
-- mountain infantry unit.  Warfare classes and military units therefore live
-- on different object levels and must not be conflated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Finite object universe used by this specimen.
------------------------------------------------------------------------

data Entity : Set where
  warfare conflict typeOfWar typeOfConflict metaclass typeEntity : Entity
  mountainWarfare skiWarfare coldWeatherWarfare : Entity
  coldWeather climate weather skiing militarySkier : Entity
  mountainGun mountainArtillery : Entity
  alpinistUnit mountainInfantryUnit : Entity
  skiersMilitaryUnit militaryUnitTypeClass mountainUnit militaryUnit skier : Entity
  alpini : Entity

------------------------------------------------------------------------
-- Wikidata properties represented as first-class values where P1963 needs to
-- talk ABOUT a property.
------------------------------------------------------------------------

data WDProperty : Set where
  p31Prop p279Prop p1963Prop practicedByProp usesProp : WDProperty
  partOfProp facetOfProp hasCauseProp hasEffectProp pointInTimeProp : WDProperty
  handledByProp associatedHazardProp fieldOfWorkProp : WDProperty

------------------------------------------------------------------------
-- Current statements, kept relation-typed.
------------------------------------------------------------------------

data P31 : Entity → Entity → Set where
  type-of-war-is-metaclass : P31 typeOfWar metaclass
  type-of-conflict-is-metaclass : P31 typeOfConflict metaclass
  cold-weather-is-climate : P31 coldWeather climate
  alpinist-unit-is-mountain-infantry : P31 alpinistUnit mountainInfantryUnit
  skiers-unit-is-military-unit-type : P31 skiersMilitaryUnit militaryUnitTypeClass


data P279 : Entity → Entity → Set where
  mountain-warfare-sub-warfare : P279 mountainWarfare warfare
  ski-sub-skiing : P279 skiWarfare skiing
  ski-sub-warfare : P279 skiWarfare warfare
  ski-sub-cold-weather-warfare : P279 skiWarfare coldWeatherWarfare
  ski-sub-mountain-warfare : P279 skiWarfare mountainWarfare
  cold-weather-warfare-sub-warfare : P279 coldWeatherWarfare warfare
  cold-weather-sub-weather : P279 coldWeather weather
  skiers-unit-sub-mountain-unit : P279 skiersMilitaryUnit mountainUnit
  skiers-unit-sub-military-unit : P279 skiersMilitaryUnit militaryUnit
  alpini-sub-mountain-infantry : P279 alpini mountainInfantryUnit
  alpini-sub-skiers-unit : P279 alpini skiersMilitaryUnit


data PracticedBy : Entity → Entity → Set where
  ski-practiced-by-military-skier : PracticedBy skiWarfare militarySkier
  cold-weather-warfare-practiced-by-military-skier :
    PracticedBy coldWeatherWarfare militarySkier


data Uses : Entity → Entity → Set where
  mountain-warfare-uses-mountain-gun : Uses mountainWarfare mountainGun
  mountain-warfare-uses-mountain-artillery : Uses mountainWarfare mountainArtillery


data FieldOfWork : Entity → Entity → Set where
  alpini-field-mountain-warfare : FieldOfWork alpini mountainWarfare

------------------------------------------------------------------------
-- Current P1963 shape already present on Q125092269 "type of conflict".
-- P1963 means "when this subject is used as object of P31, these properties
-- normally apply".  It is schema/documentation, not by itself a hard theorem.
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
-- Proposed P1963 extension for Q124867660 "type of war".
--
-- These are NOT claimed to be live statements.  They are the native Wikidata
-- way to express the property surface suggested by the positive specimens:
-- subclass location, practitioners, and things/concepts used in the activity.
------------------------------------------------------------------------

data ProposedWarP1963 : WDProperty → Set where
  war-shape-subclass : ProposedWarP1963 p279Prop
  war-shape-practiced-by : ProposedWarP1963 practicedByProp
  war-shape-uses : ProposedWarP1963 usesProp

------------------------------------------------------------------------
-- Proposed metaclass typing of the warfare classes in this specimen.
-- Again: separate from current statements so the formalisation does not rewrite
-- Wikidata merely by declaring a constructor.
------------------------------------------------------------------------

data ProposedTypeOfWar : Entity → Set where
  mountain-is-war-type : ProposedTypeOfWar mountainWarfare
  ski-is-war-type : ProposedTypeOfWar skiWarfare
  cold-weather-is-war-type : ProposedTypeOfWar coldWeatherWarfare

------------------------------------------------------------------------
-- P279 closure for query consumers.
------------------------------------------------------------------------

data P279Star : Entity → Entity → Set where
  star-refl : ∀ {x} → P279Star x x
  star-step : ∀ {x y z} → P279 x y → P279Star y z → P279Star x z

ski-under-mountain : P279Star skiWarfare mountainWarfare
ski-under-mountain = star-step ski-sub-mountain-warfare star-refl

ski-under-warfare : P279Star skiWarfare warfare
ski-under-warfare = star-step ski-sub-warfare star-refl

cold-weather-under-warfare : P279Star coldWeatherWarfare warfare
cold-weather-under-warfare =
  star-step cold-weather-warfare-sub-warfare star-refl

------------------------------------------------------------------------
-- The "cold weather" category check that killed the synthetic environment axis.
------------------------------------------------------------------------

coldWeatherHasClimateType : P31 coldWeather climate
coldWeatherHasClimateType = cold-weather-is-climate

coldWeatherHasWeatherParent : P279 coldWeather weather
coldWeatherHasWeatherParent = cold-weather-sub-weather

-- No constructor embeds coldWeather itself into the warfare P279 graph.
-- The warfare object is coldWeatherWarfare, a distinct class.

------------------------------------------------------------------------
-- Properly modelled Alpine / mountain warfare specimen.
--
-- "Alpine warfare" is an alias, so the semantic object is mountainWarfare.
-- Its current class structure is P279 warfare; its current operational
-- relations include Uses mountain gun/artillery.  The proposed missing
-- metaclass statement is P31 typeOfWar, represented separately above.
------------------------------------------------------------------------

record AlpineWarfareCurrent : Set where
  constructor alpineWarfareCurrent
  field
    superclass : P279 mountainWarfare warfare
    usesMountainGun : Uses mountainWarfare mountainGun
    usesMountainArtillery : Uses mountainWarfare mountainArtillery

canonicalAlpineWarfareCurrent : AlpineWarfareCurrent
canonicalAlpineWarfareCurrent =
  alpineWarfareCurrent
    mountain-warfare-sub-warfare
    mountain-warfare-uses-mountain-gun
    mountain-warfare-uses-mountain-artillery

record AlpineWarfareProposed : Set where
  constructor alpineWarfareProposed
  field
    current : AlpineWarfareCurrent
    metaclass : ProposedTypeOfWar mountainWarfare

canonicalAlpineWarfareProposed : AlpineWarfareProposed
canonicalAlpineWarfareProposed =
  alpineWarfareProposed canonicalAlpineWarfareCurrent mountain-is-war-type

------------------------------------------------------------------------
-- Ski warfare is the richer positive child specimen.  Its information is not
-- flattened into synthetic facets: it is literally the current relation fanout.
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
-- Object-level separation: a concrete Alpine unit is not the warfare class.
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
-- Hard conformance is stronger than P1963 suggestion.
-- A type-of-war member must at minimum be located in the warfare hierarchy;
-- richer relation witnesses may then be present without inventing new axes.
------------------------------------------------------------------------

record WarTypeConforms (x : Entity) : Set where
  constructor warTypeConforms
  field
    typed : ProposedTypeOfWar x
    underWarfare : P279Star x warfare

mountainConforms : WarTypeConforms mountainWarfare
mountainConforms =
  warTypeConforms mountain-is-war-type
    (star-step mountain-warfare-sub-warfare star-refl)

skiConforms : WarTypeConforms skiWarfare
skiConforms = warTypeConforms ski-is-war-type ski-under-warfare

coldWeatherWarfareConforms : WarTypeConforms coldWeatherWarfare
coldWeatherWarfareConforms =
  warTypeConforms cold-weather-is-war-type cold-weather-under-warfare

------------------------------------------------------------------------
-- Boundary: what the new model deliberately does NOT claim.
------------------------------------------------------------------------

record WarfareOntologyBoundary : Set where
  constructor warfareOntologyBoundary
  field
    alpineWarfareNeedsSeparateItemFromMountainWarfare : Bool
    coldWeatherIsAWeatherObject : Bool
    coldWeatherIsAWarType : Bool
    p1963IsHardConstraintByItself : Bool
    warfareClassesAndConcreteMilitaryUnitsAreSameLevel : Bool
    syntheticEnvironmentFacetRequired : Bool

canonicalWarfareOntologyBoundary : WarfareOntologyBoundary
canonicalWarfareOntologyBoundary =
  warfareOntologyBoundary false true false false false false
