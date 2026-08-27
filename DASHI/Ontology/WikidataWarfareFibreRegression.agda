module DASHI.Ontology.WikidataWarfareFibreRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_)

import DASHI.Ontology.WikidataWarfareFibreExact as W
import DASHI.Ontology.WikidataWarfareSemanticTargetExact as Q

------------------------------------------------------------------------
-- Positive inheritance case from the motivating film query.
------------------------------------------------------------------------

submarineStillDescendsToNaval :
  W.P279Star W.submarineWarfare W.navalWarfare
submarineStillDescendsToNaval = W.submarine-under-naval

submarineStillDescendsToWarfare :
  W.P279Star W.submarineWarfare W.warfare
submarineStillDescendsToWarfare = W.submarine-under-warfare

submarineFilmStillHitsNaval :
  Q.QueryHit Q.mainSubject Q.submarineFilm W.navalWarfare
submarineFilmStillHitsNaval = Q.submarineFilmHitsNavalQuery

------------------------------------------------------------------------
-- Trench warfare remains the deliberate current-graph failure specimen.
------------------------------------------------------------------------

trenchStillClassifiedAsMilitaryTactics :
  W.P31 W.trenchWarfare W.militaryTactics
trenchStillClassifiedAsMilitaryTactics = W.trench-is-military-tactics

trenchStillDescendsToStaticBattle :
  W.P279Star W.trenchWarfare W.staticBattle
trenchStillDescendsToStaticBattle = W.trench-under-static-battle

trenchCurrentWarfareProjectionStillMisses :
  W.underWarfare W.trenchWarfare ≡ false
trenchCurrentWarfareProjectionStillMisses = refl

trenchIntendedFilmConsumerStillIncludes :
  Q.intendedWarfareFilmConsumer Q.trenchFilm ≡ true
trenchIntendedFilmConsumerStillIncludes = refl

------------------------------------------------------------------------
-- Multi-inheritance is retained literally rather than normalised into fake
-- environment/platform/mechanism facets.
------------------------------------------------------------------------

skiKeepsActualRelationFanout : W.SkiWarfareShape
skiKeepsActualRelationFanout = W.canonicalSkiWarfareShape

skiStillDescendsToMountainWarfare :
  W.P279Star W.skiWarfare W.mountainWarfare
skiStillDescendsToMountainWarfare = W.ski-under-mountain

skiStillDescendsToColdWeatherWarfare :
  W.P279Star W.skiWarfare W.coldWeatherWarfare
skiStillDescendsToColdWeatherWarfare = W.ski-under-cold-weather

------------------------------------------------------------------------
-- `cold weather` and `cold-weather warfare` stay distinct object levels.
------------------------------------------------------------------------

coldWeatherStillTypedAsClimate : W.P31 W.coldWeather W.climate
coldWeatherStillTypedAsClimate = W.cold-weather-is-climate

coldWeatherStillSubWeather : W.P279 W.coldWeather W.weather
coldWeatherStillSubWeather = W.cold-weather-sub-weather

coldWeatherWarfareStillUnderWarfare :
  W.P279Star W.coldWeatherWarfare W.warfare
coldWeatherWarfareStillUnderWarfare = W.cold-weather-under-warfare

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
-- Metaclass membership and inheritance are independent obligations.
------------------------------------------------------------------------

navalCurrentMetaclassTyping : W.P31 W.navalWarfare W.typeOfWar
navalCurrentMetaclassTyping = W.naval-is-type-of-war

mountainProposedMetaclassTyping : W.ProposedTypeOfWar W.mountainWarfare
mountainProposedMetaclassTyping = W.mountain-is-war-type

mountainQueryConforms : W.WarfareQueryConforms W.mountainWarfare
mountainQueryConforms = W.mountainConforms

------------------------------------------------------------------------
-- Boundary regressions: do not regress into the tempting but wrong repairs.
------------------------------------------------------------------------

p31DoesNotReplaceP279 :
  W.WarfareOntologyBoundary.p31ReplacesP279Inheritance
    W.canonicalWarfareOntologyBoundary
  ≡ false
p31DoesNotReplaceP279 = refl

metaclassDoesNotMagicallyRepairTraversal :
  W.WarfareOntologyBoundary.metaclassTypingRepairsP279ReachabilityByItself
    W.canonicalWarfareOntologyBoundary
  ≡ false
metaclassDoesNotMagicallyRepairTraversal = refl

flatChildrenAreNotAutomaticallyDefective :
  W.WarfareOntologyBoundary.flatDirectChildrenAreAutomaticallyWrong
    W.canonicalWarfareOntologyBoundary
  ≡ false
flatChildrenAreNotAutomaticallyDefective = refl

multipleInheritanceRemainsAvailable :
  W.WarfareOntologyBoundary.multipleInheritanceIsAllowedWhenBothClassClaimsHold
    W.canonicalWarfareOntologyBoundary
  ≡ true
multipleInheritanceRemainsAvailable = refl

noSyntheticFacetVocabularyRequired :
  W.WarfareOntologyBoundary.syntheticFacetVocabularyRequired
    W.canonicalWarfareOntologyBoundary
  ≡ false
noSyntheticFacetVocabularyRequired = refl
