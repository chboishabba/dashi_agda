module DASHI.Ontology.WikidataWarfareSemanticTargetExact where

------------------------------------------------------------------------
-- NORMALISED WARFARE QUERY TARGET
--
-- `WikidataWarfareFibreExact` separates current Wikidata relations from typed
-- semantic facets.  This module adds the missing base of that fibration:
-- an explicit relation saying which class-items are warfare forms for the
-- declared warfare-film consumer.
--
-- This relation is intentionally NOT defined as `P279Star x warfare`, because
-- trench warfare is the motivating counterexample: current graph placement can
-- miss a semantically relevant warfare form.  It is also NOT P31: metaclass
-- membership and consumer-domain membership are different questions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Ontology.WikidataWarfareFibreExact as W

------------------------------------------------------------------------
-- Base fibre: which entities belong in the warfare-form query universe.
------------------------------------------------------------------------

data WarfareForm : W.Entity → Set where
  naval-form : WarfareForm W.navalWarfare
  submarine-form : WarfareForm W.submarineWarfare
  economic-form : WarfareForm W.economicWarfare
  mountain-form : WarfareForm W.mountainWarfare
  trench-form : WarfareForm W.trenchWarfare
  ski-form : WarfareForm W.skiWarfare
  unrestricted-submarine-form : WarfareForm W.unrestrictedSubmarineWarfare

isWarfareForm : W.Entity → Bool
isWarfareForm W.navalWarfare = true
isWarfareForm W.submarineWarfare = true
isWarfareForm W.economicWarfare = true
isWarfareForm W.mountainWarfare = true
isWarfareForm W.trenchWarfare = true
isWarfareForm W.skiWarfare = true
isWarfareForm W.unrestrictedSubmarineWarfare = true
isWarfareForm _ = false

------------------------------------------------------------------------
-- The central repair: current hierarchy recall and semantic-domain membership
-- are explicitly different observers.
------------------------------------------------------------------------

trenchMissedByCurrentHierarchy : W.underWarfare W.trenchWarfare ≡ false
trenchMissedByCurrentHierarchy = W.trenchMissedByCurrentWarfareProjection

trenchRecoveredByWarfareForm : isWarfareForm W.trenchWarfare ≡ true
trenchRecoveredByWarfareForm = refl

------------------------------------------------------------------------
-- Facets live over the warfare-form base rather than replacing it.
------------------------------------------------------------------------

record FacetedWarfare (x : W.Entity) : Set where
  constructor facetedWarfare
  field
    warfareForm : WarfareForm x

navalSemanticObject : FacetedWarfare W.navalWarfare
navalSemanticObject = facetedWarfare naval-form

submarineSemanticObject : FacetedWarfare W.submarineWarfare
submarineSemanticObject = facetedWarfare submarine-form

economicSemanticObject : FacetedWarfare W.economicWarfare
economicSemanticObject = facetedWarfare economic-form

mountainSemanticObject : FacetedWarfare W.mountainWarfare
mountainSemanticObject = facetedWarfare mountain-form

trenchSemanticObject : FacetedWarfare W.trenchWarfare
trenchSemanticObject = facetedWarfare trench-form

skiSemanticObject : FacetedWarfare W.skiWarfare
skiSemanticObject = facetedWarfare ski-form

unrestrictedSubmarineSemanticObject : FacetedWarfare W.unrestrictedSubmarineWarfare
unrestrictedSubmarineSemanticObject = facetedWarfare unrestricted-submarine-form

------------------------------------------------------------------------
-- Actual intended relation bundle for representative items.
------------------------------------------------------------------------

submarineBundle :
  WarfareForm W.submarineWarfare ×
  W.P279Star W.submarineWarfare W.navalWarfare ×
  W.HasFacet W.submarineWarfare W.operationalDomain W.navalDomain ×
  W.HasFacet W.submarineWarfare W.platform W.submarinePlatform
submarineBundle =
  submarine-form ,
  W.submarine-under-naval ,
  W.submarine-naval-domain ,
  W.submarine-platform

economicBundle :
  WarfareForm W.economicWarfare ×
  W.P31 W.economicWarfare W.typeOfConflict ×
  W.P279 W.economicWarfare W.warfare ×
  W.HasFacet W.economicWarfare W.mechanism W.economicMechanism
economicBundle =
  economic-form ,
  W.economicP31TypeOfConflict ,
  W.economicP279Warfare ,
  W.economic-mechanism

mountainBundle :
  WarfareForm W.mountainWarfare ×
  W.P279 W.mountainWarfare W.warfare ×
  W.HasFacet W.mountainWarfare W.environment W.mountainEnvironment
mountainBundle =
  mountain-form ,
  W.mountain-sub-warfare ,
  W.mountain-environment

trenchBundle :
  WarfareForm W.trenchWarfare ×
  W.P31 W.trenchWarfare W.militaryTactics ×
  W.P279 W.trenchWarfare W.staticBattle ×
  W.HasFacet W.trenchWarfare W.tacticDoctrine W.trenchTactic
trenchBundle =
  trench-form ,
  W.trench-is-military-tactics ,
  W.trench-sub-static-battle ,
  W.trench-tactic

------------------------------------------------------------------------
-- Query contract.
--
-- A film/subject consumer first ranges over WarfareForm, then refines by one or
-- more typed facets.  P31 and P279 remain available as independent metadata and
-- inheritance relations; neither is overloaded as the universal facet axis.
------------------------------------------------------------------------

record WarfareSemanticQueryBoundary : Set where
  constructor warfareSemanticQueryBoundary
  field
    warfareDomainDefinedByBareP279Closure : Bool
    warfareDomainDefinedByBareP31 : Bool
    warfareFormBaseIsIndependentRelation : Bool
    facetsRefineWarfareFormBase : Bool
    currentP31AndP279AreRetained : Bool

canonicalWarfareSemanticQueryBoundary : WarfareSemanticQueryBoundary
canonicalWarfareSemanticQueryBoundary =
  warfareSemanticQueryBoundary false false true true true
