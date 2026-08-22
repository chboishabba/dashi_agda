module DASHI.Ontology.WikidataWarfareFibreRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Ontology.WikidataWarfareFibreExact as W

------------------------------------------------------------------------
-- Alpine warfare is mountain warfare: one object, alias-level naming.
------------------------------------------------------------------------

alpineModelKeepsCurrentMountainStructure : W.AlpineWarfareCurrent
alpineModelKeepsCurrentMountainStructure = W.canonicalAlpineWarfareCurrent

alpineModelAddsOnlyMetaclassTyping : W.AlpineWarfareProposed
alpineModelAddsOnlyMetaclassTyping = W.canonicalAlpineWarfareProposed

------------------------------------------------------------------------
-- Ski warfare remains a literal multi-parent positive specimen.
------------------------------------------------------------------------

skiKeepsActualRelationFanout : W.SkiWarfareShape
skiKeepsActualRelationFanout = W.canonicalSkiWarfareShape

skiStillDescendsToMountainWarfare :
  W.P279Star W.skiWarfare W.mountainWarfare
skiStillDescendsToMountainWarfare = W.ski-under-mountain

------------------------------------------------------------------------
-- Cold weather itself is not promoted into the warfare type lattice.
------------------------------------------------------------------------

coldWeatherStillTypedAsClimate : W.P31 W.coldWeather W.climate
coldWeatherStillTypedAsClimate = W.coldWeatherHasClimateType

coldWeatherStillSubWeather : W.P279 W.coldWeather W.weather
coldWeatherStillSubWeather = W.coldWeatherHasWeatherParent

------------------------------------------------------------------------
-- Unit layer remains separate from warfare-class layer.
------------------------------------------------------------------------

idfAlpinistUnitStillUnitTyped : W.P31 W.alpinistUnit W.mountainInfantryUnit
idfAlpinistUnitStillUnitTyped = W.alpinistUnitIsUnitTyped

alpiniStillBridgesUnitClassToWarfareField :
  W.P279 W.alpini W.mountainInfantryUnit ×
  W.P279 W.alpini W.skiersMilitaryUnit ×
  W.FieldOfWork W.alpini W.mountainWarfare
alpiniStillBridgesUnitClassToWarfareField =
  W.alpiniLinksUnitStructureBackToWarfareField

------------------------------------------------------------------------
-- Metaclass/P1963 shape: suggested properties and hard conformance stay apart.
------------------------------------------------------------------------

warTypeSuggestsSubclassProperty : W.ProposedWarP1963 W.p279Prop
warTypeSuggestsSubclassProperty = W.war-shape-subclass

warTypeSuggestsPractitionerProperty : W.ProposedWarP1963 W.practicedByProp
warTypeSuggestsPractitionerProperty = W.war-shape-practiced-by

warTypeSuggestsUsesProperty : W.ProposedWarP1963 W.usesProp
warTypeSuggestsUsesProperty = W.war-shape-uses

mountainWarTypeConforms : W.WarTypeConforms W.mountainWarfare
mountainWarTypeConforms = W.mountainConforms

skiWarTypeConforms : W.WarTypeConforms W.skiWarfare
skiWarTypeConforms = W.skiConforms

coldWeatherWarTypeConforms : W.WarTypeConforms W.coldWeatherWarfare
coldWeatherWarTypeConforms = W.coldWeatherWarfareConforms

------------------------------------------------------------------------
-- Guard the rejected synthetic reading.
------------------------------------------------------------------------

noSyntheticEnvironmentFacetRequired :
  W.WarfareOntologyBoundary.syntheticEnvironmentFacetRequired
    W.canonicalWarfareOntologyBoundary
  ≡ false
noSyntheticEnvironmentFacetRequired = refl

coldWeatherIsNotPromotedToWarType :
  W.WarfareOntologyBoundary.coldWeatherIsAWarType
    W.canonicalWarfareOntologyBoundary
  ≡ false
coldWeatherIsNotPromotedToWarType = refl
