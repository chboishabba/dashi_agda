module DASHI.Core.AssumptionIndexedReopeningExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Proof-carrying state whose validity is explicitly conditional on assumptions,
-- with alternative support routes and selective reopening.  This strengthens a
-- plain dependency DAG: one broken route need not invalidate a claim when an
-- independent sufficient route survives.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record AssumptionIndexedReceipt
    (Carrier Assumption : Set)
    (Holds : Assumption → Set)
    (Valid : Carrier → Set) : Set₁ where
  constructor assumptionIndexedReceipt
  field
    state : Carrier
    Needed : Assumption → Set
    validityFromAssumptions :
      ((assumption : Assumption) →
       Needed assumption →
       Holds assumption) →
      Valid state
    provenanceReference : String

open AssumptionIndexedReceipt public

record AlternativeSupportSystem
    (Change Route : Set) : Set₁ where
  constructor alternativeSupportSystem
  field
    Hits : Change → Route → Set
    routeDescription : Route → String

open AlternativeSupportSystem public

GloballyInvalidates :
  ∀ {Change Route} →
  AlternativeSupportSystem Change Route →
  Change → Set
GloballyInvalidates system change =
  ∀ route → Hits system change route

record SurvivingSupportRoute
    {Change Route : Set}
    (system : AlternativeSupportSystem Change Route)
    (change : Change) : Set₁ where
  constructor survivingSupportRoute
  field
    route : Route
    notHit : Hits system change route → ⊥

open SurvivingSupportRoute public

survivingRouteRefutesGlobalInvalidation :
  ∀ {Change Route}
    {system : AlternativeSupportSystem Change Route}
    {change : Change} →
  SurvivingSupportRoute system change →
  GloballyInvalidates system change →
  ⊥
survivingRouteRefutesGlobalInvalidation surviving global =
  notHit surviving (global (route surviving))

record EvidenceLineage
    (Root Evidence : Set) : Set₁ where
  constructor evidenceLineage
  field
    RootOf : Root → Evidence → Set
    rootLabel : Root → String

open EvidenceLineage public

IndependentEvidence :
  ∀ {Root Evidence} →
  EvidenceLineage Root Evidence →
  Evidence → Evidence → Set
IndependentEvidence lineage left right =
  ∀ root →
  RootOf lineage root left →
  RootOf lineage root right →
  ⊥

record SharedEvidenceRoot
    {Root Evidence : Set}
    (lineage : EvidenceLineage Root Evidence)
    (left right : Evidence) : Set₁ where
  constructor sharedEvidenceRoot
  field
    root : Root
    rootSupportsLeft : RootOf lineage root left
    rootSupportsRight : RootOf lineage root right

open SharedEvidenceRoot public

sharedRootRefutesIndependence :
  ∀ {Root Evidence}
    {lineage : EvidenceLineage Root Evidence}
    {left right : Evidence} →
  SharedEvidenceRoot lineage left right →
  IndependentEvidence lineage left right →
  ⊥
sharedRootRefutesIndependence shared independent =
  independent
    (root shared)
    (rootSupportsLeft shared)
    (rootSupportsRight shared)

record ConsumerReopeningPolicy
    (Change Consumer : Set) : Set₁ where
  constructor consumerReopeningPolicy
  field
    Reopen : Change → Consumer → Set
    policyReference : Consumer → String

open ConsumerReopeningPolicy public

record SelectiveReopeningWitness
    {Change Consumer : Set}
    (policy : ConsumerReopeningPolicy Change Consumer)
    (change : Change) : Set₁ where
  constructor selectiveReopeningWitness
  field
    affectedConsumer : Consumer
    requiresReopening :
      Reopen policy change affectedConsumer

open SelectiveReopeningWitness public

record RouteCarriedValidity
    (Carrier Route : Set)
    (Valid : Carrier → Set) : Set₁ where
  constructor routeCarriedValidity
  field
    state : Carrier
    valid : Valid state
    supportingRoute : Route
    routeProvenance : String

open RouteCarriedValidity public

record AssumptionIndexedReopeningBoundary : Set where
  constructor assumptionIndexedReopeningBoundary
  field
    validityMayBeConditionalOnAssumptions : Bool
    oneBrokenRouteNeedNotInvalidateClaim : Bool
    allSupportRoutesHitIsStrongerThanOneDependencyChanged : Bool
    evidenceIndependenceNeedsLineage : Bool
    differentModalitiesDoNotGuaranteeIndependence : Bool
    reopeningCanBeConsumerSpecific : Bool
    survivingSupportCanBlockGlobalInvalidation : Bool
    provenanceDoesNotCreateTruthAuthority : Bool

open AssumptionIndexedReopeningBoundary public

canonicalAssumptionIndexedReopeningBoundary :
  AssumptionIndexedReopeningBoundary
canonicalAssumptionIndexedReopeningBoundary =
  assumptionIndexedReopeningBoundary
    true true true true true true true true
