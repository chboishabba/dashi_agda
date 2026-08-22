module DASHI.Ontology.WikidataWarfareFibreRegression where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Ontology.WikidataWarfareFibreExact as W

------------------------------------------------------------------------
-- Repo-native consumer-descent witnesses for the warfare specimen.
------------------------------------------------------------------------

p31AloneDoesNotSupportNavalConsumer :
  Descent.ConsumerNonDescentWitness W.p31Observation W.underNaval
p31AloneDoesNotSupportNavalConsumer =
  Descent.consumerNonDescentWitness
    W.submarineWarfare
    W.mountainWarfare
    refl
    W.navalOutcomeDoesNotDescendThroughThatCollision

p31AloneCannotBeSufficientForNavalConsumer :
  Descent.ConsumerSufficient W.p31Observation W.underNaval → ⊥
p31AloneCannotBeSufficientForNavalConsumer =
  Descent.nonDescentWitnessBlocksSufficiency
    p31AloneDoesNotSupportNavalConsumer

------------------------------------------------------------------------
-- Adding the coarse fact "under warfare" still does not repair the fibre.
------------------------------------------------------------------------

record MetaWarfareObservation : Set where
  constructor metaWarfareObservation
  field
    meta : W.P31Observation
    inWarfare : Bool

observeMetaAndWarfare : W.Entity → MetaWarfareObservation
observeMetaAndWarfare x =
  metaWarfareObservation (W.p31Observation x) (W.underWarfare x)

metaAndWarfareCollision :
  observeMetaAndWarfare W.submarineWarfare
  ≡ observeMetaAndWarfare W.mountainWarfare
metaAndWarfareCollision = refl

p31PlusWarfareDoesNotSupportNavalConsumer :
  Descent.ConsumerNonDescentWitness observeMetaAndWarfare W.underNaval
p31PlusWarfareDoesNotSupportNavalConsumer =
  Descent.consumerNonDescentWitness
    W.submarineWarfare
    W.mountainWarfare
    metaAndWarfareCollision
    W.navalOutcomeDoesNotDescendThroughThatCollision

p31PlusWarfareCannotBeSufficientForNavalConsumer :
  Descent.ConsumerSufficient observeMetaAndWarfare W.underNaval → ⊥
p31PlusWarfareCannotBeSufficientForNavalConsumer =
  Descent.nonDescentWitnessBlocksSufficiency
    p31PlusWarfareDoesNotSupportNavalConsumer

------------------------------------------------------------------------
-- Current-Wikidata sanity cases remain available alongside the normalised
-- facets.  P31 and P279 are complementary axes, not replacements.
------------------------------------------------------------------------

economicKeepsMetaclassAndInheritance :
  W.P31 W.economicWarfare W.typeOfConflict ×
  W.P279 W.economicWarfare W.warfare
economicKeepsMetaclassAndInheritance =
  W.economicP31TypeOfConflict , W.economicP279Warfare

navalKeepsMetaclassAndInheritance :
  W.P31 W.navalWarfare W.typeOfWar ×
  W.P279 W.navalWarfare W.warfare
navalKeepsMetaclassAndInheritance =
  W.navalP31TypeOfWar , W.navalP279Warfare

------------------------------------------------------------------------
-- Typed facet refinement separates semantic dimensions which a flat parent
-- relation need not distinguish.
------------------------------------------------------------------------

flatSiblingsCanRetainDifferentSemanticAxes :
  W.P279 W.mountainWarfare W.warfare ×
  W.P279 W.economicWarfare W.warfare ×
  W.HasFacet W.mountainWarfare W.environment W.mountainEnvironment ×
  W.HasFacet W.economicWarfare W.mechanism W.economicMechanism
flatSiblingsCanRetainDifferentSemanticAxes =
  W.mountain-sub-warfare ,
  W.economic-sub-warfare ,
  W.mountain-environment ,
  W.economic-mechanism

submarineRetainsHierarchyDomainAndPlatform :
  W.P279Star W.submarineWarfare W.navalWarfare ×
  W.HasFacet W.submarineWarfare W.operationalDomain W.navalDomain ×
  W.HasFacet W.submarineWarfare W.platform W.submarinePlatform
submarineRetainsHierarchyDomainAndPlatform =
  W.submarine-under-naval ,
  W.submarine-naval-domain ,
  W.submarine-platform

trenchStillExposesCurrentRecallDefect :
  W.underWarfare W.trenchWarfare ≡ Agda.Builtin.Bool.false
trenchStillExposesCurrentRecallDefect =
  W.trenchMissedByCurrentWarfareProjection
