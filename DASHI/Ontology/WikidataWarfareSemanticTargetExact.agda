module DASHI.Ontology.WikidataWarfareSemanticTargetExact where

------------------------------------------------------------------------
-- WARFARE FILM QUERY: CONSUMER DESCENT / FAILURE WITNESS
--
-- Schemathings' actual consumer is not "draw a prettier warfare tree". It is:
--
--   film --P921/P180--> specific warfare class --P279*--> requested class
--
-- e.g. a submarine-warfare film should be returned by a naval-warfare query.
--
-- This module therefore formalises the query itself, the successful submarine
-- descent, the trench miss, and the exact DASHI fibre witness showing that bare
-- current-P279 reachability is not sufficient for the intended warfare-domain
-- consumer while the graph is incomplete.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Ontology.WikidataWarfareFibreExact as W

------------------------------------------------------------------------
-- Intended semantic population for this finite specimen.
--
-- This is NOT proposed as a new Wikidata property. It is the fine semantic
-- judgement against which the existing graph-based query is being tested.
------------------------------------------------------------------------

data WarfareForm : W.Entity → Set where
  naval-form : WarfareForm W.navalWarfare
  submarine-form : WarfareForm W.submarineWarfare
  economic-form : WarfareForm W.economicWarfare
  mountain-form : WarfareForm W.mountainWarfare
  cold-weather-form : WarfareForm W.coldWeatherWarfare
  ski-form : WarfareForm W.skiWarfare
  trench-form : WarfareForm W.trenchWarfare

isWarfareForm : W.Entity → Bool
isWarfareForm W.navalWarfare = true
isWarfareForm W.submarineWarfare = true
isWarfareForm W.economicWarfare = true
isWarfareForm W.mountainWarfare = true
isWarfareForm W.coldWeatherWarfare = true
isWarfareForm W.skiWarfare = true
isWarfareForm W.trenchWarfare = true
isWarfareForm _ = false

------------------------------------------------------------------------
-- Class-level non-descent.
--
-- trench warfare and military tactics have the SAME current observation for
-- the question "does P279* reach warfare?": false. But the intended warfare-
-- form consumer says true for trench warfare and false for military tactics.
-- Therefore intended domain membership cannot factor through that Bool.
------------------------------------------------------------------------

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

trenchAndTacticsSameCurrentProjection :
  W.underWarfare W.trenchWarfare ≡ W.underWarfare W.militaryTactics
trenchAndTacticsSameCurrentProjection = refl

trenchAndTacticsDifferentSemanticOutcome :
  isWarfareForm W.trenchWarfare ≡ isWarfareForm W.militaryTactics → ⊥
trenchAndTacticsDifferentSemanticOutcome = trueNotFalse

currentP279ProjectionNonDescent :
  Descent.ConsumerNonDescentWitness W.underWarfare isWarfareForm
currentP279ProjectionNonDescent =
  Descent.consumerNonDescentWitness
    W.trenchWarfare
    W.militaryTactics
    trenchAndTacticsSameCurrentProjection
    trenchAndTacticsDifferentSemanticOutcome

------------------------------------------------------------------------
-- Film surface. P921 (main subject) and P180 (depicts) are kept as distinct
-- assertion channels but share the same P279* class descent afterwards.
------------------------------------------------------------------------

data Film : Set where
  submarineFilm trenchFilm weatherFilm : Film

data FilmProperty : Set where
  mainSubject depicts : FilmProperty

data FilmAssertion : FilmProperty → Film → W.Entity → Set where
  submarine-main-subject :
    FilmAssertion mainSubject submarineFilm W.submarineWarfare
  trench-main-subject :
    FilmAssertion mainSubject trenchFilm W.trenchWarfare
  weather-main-subject :
    FilmAssertion mainSubject weatherFilm W.coldWeather
  trench-depicts :
    FilmAssertion depicts trenchFilm W.trenchWarfare

------------------------------------------------------------------------
-- Exact logical reading of
--
--   ?film wdt:P921/wdt:P279* TARGET
--
-- (or the P180 version). A hit carries the specific asserted subject and an
-- actual P279* proof from that subject to the query target.
------------------------------------------------------------------------

record QueryHit
    (property : FilmProperty)
    (film : Film)
    (target : W.Entity) : Set where
  constructor queryHit
  field
    subject : W.Entity
    asserted : FilmAssertion property film subject
    descends : W.P279Star subject target

submarineFilmHitsNavalQuery :
  QueryHit mainSubject submarineFilm W.navalWarfare
submarineFilmHitsNavalQuery =
  queryHit W.submarineWarfare
    submarine-main-subject
    W.submarine-under-naval

submarineFilmHitsWarfareQuery :
  QueryHit mainSubject submarineFilm W.warfare
submarineFilmHitsWarfareQuery =
  queryHit W.submarineWarfare
    submarine-main-subject
    W.submarine-under-warfare

------------------------------------------------------------------------
-- Film-level current query observation versus intended domain consumer.
--
-- weatherFilm is a negative control: its subject is `cold weather`, not
-- `cold-weather warfare`. The current query correctly rejects it. trenchFilm is
-- semantically a warfare-form film but is also rejected by the current P279*
-- warfare query because the class path exits through static battle.
------------------------------------------------------------------------

currentWarfareFilmQuery : Film → Bool
currentWarfareFilmQuery submarineFilm = W.underWarfare W.submarineWarfare
currentWarfareFilmQuery trenchFilm = W.underWarfare W.trenchWarfare
currentWarfareFilmQuery weatherFilm = W.underWarfare W.coldWeather

intendedWarfareFilmConsumer : Film → Bool
intendedWarfareFilmConsumer submarineFilm = true
intendedWarfareFilmConsumer trenchFilm = true
intendedWarfareFilmConsumer weatherFilm = false

submarineRetrieved : currentWarfareFilmQuery submarineFilm ≡ true
submarineRetrieved = refl

trenchSilentlyMissed : currentWarfareFilmQuery trenchFilm ≡ false
trenchSilentlyMissed = refl

trenchShouldBeInIntendedDomain : intendedWarfareFilmConsumer trenchFilm ≡ true
trenchShouldBeInIntendedDomain = refl

weatherCorrectlyExcluded : intendedWarfareFilmConsumer weatherFilm ≡ false
weatherCorrectlyExcluded = refl

trenchAndWeatherSameQuerySurface :
  currentWarfareFilmQuery trenchFilm ≡ currentWarfareFilmQuery weatherFilm
trenchAndWeatherSameQuerySurface = refl

trenchAndWeatherDifferentConsumerOutcome :
  intendedWarfareFilmConsumer trenchFilm ≡
  intendedWarfareFilmConsumer weatherFilm → ⊥
trenchAndWeatherDifferentConsumerOutcome = trueNotFalse

filmQueryNonDescent :
  Descent.ConsumerNonDescentWitness
    currentWarfareFilmQuery intendedWarfareFilmConsumer
filmQueryNonDescent =
  Descent.consumerNonDescentWitness
    trenchFilm
    weatherFilm
    trenchAndWeatherSameQuerySurface
    trenchAndWeatherDifferentConsumerOutcome

------------------------------------------------------------------------
-- What metaclass population does and does NOT buy us.
--
-- P31 type-of-war can define/check a population of warfare class-items. But a
-- film query of the form P921/P279* still needs P279 connectivity. Thus the
-- proper repair has two independent obligations:
--
--   1. population/schema: appropriate P31 metaclass typing;
--   2. inheritance/query: semantically valid P279 placement.
--
-- Neither obligation substitutes for the other.
------------------------------------------------------------------------

record WarfareRepairContract : Set where
  constructor warfareRepairContract
  field
    retainSpecificFilmSubject : Bool
    retainP279Inheritance : Bool
    populateMetaclassWhereAppropriate : Bool
    metaclassTypingAloneRepairsFilmQuery : Bool
    addP279OnlyWhenUniversalSubclassClaimHolds : Bool
    directChildOfWarfareRequiresInventedIntermediate : Bool
    trenchNeedsQueryConnectivityIfItIsSemanticallyWarfare : Bool

canonicalWarfareRepairContract : WarfareRepairContract
canonicalWarfareRepairContract =
  warfareRepairContract true true true false true false true
