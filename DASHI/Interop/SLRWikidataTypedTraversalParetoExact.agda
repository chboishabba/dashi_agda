module DASHI.Interop.SLRWikidataTypedTraversalParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRWorldResearchIterationBudgetExact as Budget

------------------------------------------------------------------------
-- TYPED WIKIDATA / WIKIPEDIA TRAVERSAL PARETO
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_world_research_route_pareto.py
--   tools/slr-discourse-reconstruct/slr_world_research_typed_route_frontier.py
--   tools/slr-discourse-reconstruct/run_world_research_typed_route_round.sh
--
-- SensibLaw alignment:
-- * provider-native Q/P coordinates are retained across acquisition transports;
-- * QID identity and provider/acquisition provenance are distinct;
-- * P31/P279 are diagnostic/control-plane class relations, not authoritative
--   imports into the internal legal ontology;
-- * P31/P279 mixed-order, SCC and metaclass-heavy regions require review;
-- * parthood relations remain typed review surfaces rather than automatic truth.
--
-- Execution discipline:
-- * selecting a typed route and executing that route are separate obligations;
-- * the bounded inner round must consume the exact selected target-QID set;
-- * a generic Pareto replanner may not silently substitute unrelated QIDs.
------------------------------------------------------------------------

data TraversalRouteFamily : Set where
  wikidataInstanceClass : TraversalRouteFamily       -- P31
  wikidataSubclassParent : TraversalRouteFamily      -- P279
  wikidataPartOf : TraversalRouteFamily              -- P361
  wikidataHasPart : TraversalRouteFamily              -- P527
  wikidataAdminLocation : TraversalRouteFamily       -- P131
  wikidataCountry : TraversalRouteFamily             -- P17
  wikidataFacetOf : TraversalRouteFamily             -- P1269
  wikidataOtherProperty : TraversalRouteFamily
  wikipediaCurrentFirstLink : TraversalRouteFamily
  wikipediaRelated : TraversalRouteFamily

record TypedTraversalAction : Set where
  constructor typedTraversalAction
  field
    sourceQidReference : String
    propertyPidReference : String
    targetQidReference : String
    routeFamily : TraversalRouteFamily
    routeDirectionReference : String
    consumerGapCoverageReference : String
    sourceSurfaceSupportReference : String
    rootQidSupportReference : String
    routeSpecificityReference : String
    priorYieldReference : String
    sensibLawControlPlaneOnly : Bool
    sensibLawHotspotSensitive : Bool
    typedPropertyCreatesClaimTruth : Bool
    qidIdentityCreatesOntologyTransplant : Bool
    providerTransportCreatesEntityIdentity : Bool
    currentFirstLinkCreatesHistoricalIbrahimEdge : Bool
    paretoDimensionsScalarized : Bool
    frontierRankCreatesTruthRank : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open TypedTraversalAction public

record TypedTraversalBoundary : Set where
  constructor typedTraversalBoundary
  field
    p31AndP279RetainDistinctRouteFamilies : Bool
    mixedOrderAndSccSensitivityRetained : Bool
    parthoodTypingRetained : Bool
    parentRepairMayFollowLowYieldSpecificRoute : Bool
    childOrInstanceRepairMayFollowOverBroadParent : Bool
    currentFirstLinkMayNavigate : Bool
    currentFirstLinkPaysHistoricalIbrahimEquivalence : Bool
    mixedRouteRoundPaysCausalYield : Bool
    observedRouteYieldCreatesTruth : Bool
    typedPropertyCreatesCanonicalInternalOntology : Bool
    providerTransportCreatesEntityIdentity : Bool
    paretoRequiresWeightedScore : Bool
    selectedRouteMustMatchExecutedTarget : Bool
    innerPlannerMaySubstituteTypedRouteTarget : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open TypedTraversalBoundary public

canonicalTypedTraversalBoundary : TypedTraversalBoundary
canonicalTypedTraversalBoundary =
  typedTraversalBoundary
    true true true
    true true
    true false
    false false false false false
    true false
    true false

record RouteExecutionWeld : Set where
  constructor routeExecutionWeld
  field
    schemaReference : String
    typedRoutePlanReference : String
    syntheticClosureReference : String
    innerBudgetPlanReference : String
    selectedTargetsMatch : Bool
    innerReplanningChangedTargets : Bool
    selectionCreatesTruth : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open RouteExecutionWeld public

canonicalRouteExecutionWeld : RouteExecutionWeld
canonicalRouteExecutionWeld =
  routeExecutionWeld
    "slr-world-research-typed-route-frontier-v1"
    "typed-route-plan.json"
    "typed-route-input-closure.json"
    "budget-plan.json"
    true false false true false

record RouteYieldObservation : Set where
  constructor routeYieldObservation
  field
    routeFamilyReference : String
    observedRoundsReference : String
    trustedSingleFamilyRoundsReference : String
    contractedOldGapsReference : String
    retiredObligationsReference : String
    newGapAtomsReference : String
    networkRequestsReference : String
    atomsAddedReference : String
    causalAttributionPaid : Bool
    routeYieldCreatesTruth : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open RouteYieldObservation public

canonicalRouteYieldObservation : RouteYieldObservation
canonicalRouteYieldObservation =
  routeYieldObservation
    "route_family"
    "observed_rounds"
    "trusted_single_family_rounds"
    "contracted_old_gaps"
    "retired_obligations"
    "new_gap_atoms"
    "network_requests"
    "atoms_added"
    false false true false

record SensibLawWikidataControlPlaneAnchor : Set where
  constructor sensibLawWikidataControlPlaneAnchor
  field
    qAndPCoordinatesProviderNative : Bool
    acquisitionSourceSeparateFromEntityCoordinate : Bool
    ordinaryLookupPaysIdentityProof : Bool
    externalClassStructureIsNormativeLegalOntology : Bool
    p31P279DiagnosticsIncludeMixedOrder : Bool
    p279DiagnosticsIncludeSccs : Bool
    diagnosticsIncludeMetaclassCandidates : Bool
    diagnosticsMayIncludeParthoodTyping : Bool

open SensibLawWikidataControlPlaneAnchor public

canonicalSensibLawWikidataControlPlaneAnchor : SensibLawWikidataControlPlaneAnchor
canonicalSensibLawWikidataControlPlaneAnchor =
  sensibLawWikidataControlPlaneAnchor
    true true false false true true true true

budgetAnchor : Budget.WorldResearchIterationBudget
budgetAnchor = Budget.canonicalWorldResearchIterationBudget

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TypedPropertyCreatesClaimTruth : Set where
data QidIdentityTransplantsExternalOntology : Set where
data ProviderTransportIsEntityIdentity : Set where
data CurrentFirstLinkIsHistoricalIbrahimEdge : Set where
data MixedRouteObservationPaysCausalYield : Set where
data RouteYieldCreatesTruth : Set where
data P31P279ImportedAsCanonicalLegalOntology : Set where
data ParetoRouteChoiceRequiresScalarScore : Set where
data InnerPlannerMaySubstituteTypedRouteTarget : Set where
data RouteSelectionIsRouteExecution : Set where

typedPropertyDoesNotCreateClaimTruth : TypedPropertyCreatesClaimTruth → ⊥
typedPropertyDoesNotCreateClaimTruth ()

qidIdentityDoesNotTransplantOntology : QidIdentityTransplantsExternalOntology → ⊥
qidIdentityDoesNotTransplantOntology ()

providerTransportDoesNotCreateEntityIdentity : ProviderTransportIsEntityIdentity → ⊥
providerTransportDoesNotCreateEntityIdentity ()

currentFirstLinkDoesNotPayHistoricalIbrahimEdge : CurrentFirstLinkIsHistoricalIbrahimEdge → ⊥
currentFirstLinkDoesNotPayHistoricalIbrahimEdge ()

mixedRouteObservationDoesNotPayCausalYield : MixedRouteObservationPaysCausalYield → ⊥
mixedRouteObservationDoesNotPayCausalYield ()

routeYieldDoesNotCreateTruth : RouteYieldCreatesTruth → ⊥
routeYieldDoesNotCreateTruth ()

p31p279DoNotBecomeCanonicalLegalOntology : P31P279ImportedAsCanonicalLegalOntology → ⊥
p31p279DoNotBecomeCanonicalLegalOntology ()

routeParetoDoesNotRequireScalarScore : ParetoRouteChoiceRequiresScalarScore → ⊥
routeParetoDoesNotRequireScalarScore ()

innerPlannerCannotSubstituteTypedRouteTarget : InnerPlannerMaySubstituteTypedRouteTarget → ⊥
innerPlannerCannotSubstituteTypedRouteTarget ()

routeSelectionIsNotExecutionWithoutWeld : RouteSelectionIsRouteExecution → ⊥
routeSelectionIsNotExecutionWithoutWeld ()
