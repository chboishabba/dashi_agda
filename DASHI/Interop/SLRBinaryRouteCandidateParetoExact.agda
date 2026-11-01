module DASHI.Interop.SLRBinaryRouteCandidateParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRBinaryWorldWireParityExact as WorldWire
import DASHI.Interop.SLRResidualDrivenProducerPlannerExact as Producer

------------------------------------------------------------------------
-- BINARY ROUTE-CANDIDATE / PARETO SELECTION PARITY
--
-- Runtime owner:
--   chboishabba/slr :: crates/sl-route-selector
--
-- SLRG v1 carries candidate id, producer family, route family,
-- source/target/property references and ten explicit Pareto coordinates.
-- No weighted sum or truth rank exists in the ABI.
------------------------------------------------------------------------

routeCandidateWireVersion : Nat
routeCandidateWireVersion = 1

data RouteFamily : Set where
  wikidataProperty : RouteFamily
  wikipediaArticle : RouteFamily
  revisionHistory : RouteFamily
  primarySourceSearch : RouteFamily
  measurementSourceSearch : RouteFamily
  comparatorSourceSearch : RouteFamily
  parserRepair : RouteFamily

routeFamilyTag : RouteFamily → Nat
routeFamilyTag wikidataProperty = 1
routeFamilyTag wikipediaArticle = 2
routeFamilyTag revisionHistory = 3
routeFamilyTag primarySourceSearch = 4
routeFamilyTag measurementSourceSearch = 5
routeFamilyTag comparatorSourceSearch = 6
routeFamilyTag parserRepair = 7

data ParetoDirection : Set where
  maximise : ParetoDirection
  minimise : ParetoDirection

data RouteAxis : Set where
  crossLanguageGapCoverage : RouteAxis
  sourceSurfaceSupport : RouteAxis
  rootQIDSupport : RouteAxis
  typedPropertySupport : RouteAxis
  routeSpecificity : RouteAxis
  yieldHistoryObserved : RouteAxis
  priorContractedOldGaps : RouteAxis
  priorRetiredObligations : RouteAxis
  priorNewGapAtoms : RouteAxis
  priorNetworkRequests : RouteAxis

routeAxisDirection : RouteAxis → ParetoDirection
routeAxisDirection crossLanguageGapCoverage = maximise
routeAxisDirection sourceSurfaceSupport = maximise
routeAxisDirection rootQIDSupport = maximise
routeAxisDirection typedPropertySupport = maximise
routeAxisDirection routeSpecificity = maximise
routeAxisDirection yieldHistoryObserved = maximise
routeAxisDirection priorContractedOldGaps = maximise
routeAxisDirection priorRetiredObligations = maximise
routeAxisDirection priorNewGapAtoms = minimise
routeAxisDirection priorNetworkRequests = minimise

selectedRouteWorldWireKindTag : Nat
selectedRouteWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.routeAction

record BinaryRouteCandidateParetoParity : Set where
  constructor binaryRouteCandidateParetoParity
  field
    candidateMagicIsSLRG : Bool
    candidateVersionIsOne : Bool
    producerTagsReuseResidualPlanner : Bool
    routeFamilyTagsOneThroughSevenExact : Bool
    allTenAxesExplicit : Bool
    firstEightAxesMaximised : Bool
    lastTwoAxesMinimised : Bool
    candidateOnlyByteIsOne : Bool
    semanticPromotionByteIsZero : Bool
    producerFamilyMustMatchIntent : Bool
    dominatedCandidateSelected : Bool
    nondominatedTradeoffMayRemain : Bool
    dimensionsScalarized : Bool
    frontierRankIsTruthRank : Bool
    selectedBodyMagicIsRTA2 : Bool
    selectedRouteUsesWorldWireKindSix : Bool
    selectedRouteRetainsSourceTargetProperty : Bool
    selectedRouteCreatesClaimTruth : Bool
    selectedRouteCreatesSemanticAuthority : Bool
    jsonTransportUsed : Bool
    regexParserUsed : Bool

open BinaryRouteCandidateParetoParity public

canonicalBinaryRouteCandidateParetoParity : BinaryRouteCandidateParetoParity
canonicalBinaryRouteCandidateParetoParity =
  binaryRouteCandidateParetoParity
    true true true true true true true true true true
    false true false false true true true false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ScalarizedRouteTruthRank : Set where
data DominatedCandidateMustBeSelected : Set where
data SelectedRouteCreatesClaimTruth : Set where
data SelectedRouteCreatesSemanticAuthority : Set where
data RouteSelectorUsesJson : Set where
data RouteSelectorUsesRegex : Set where

routeSelectionIsNotScalarTruthRanking : ScalarizedRouteTruthRank → ⊥
routeSelectionIsNotScalarTruthRanking ()

dominatedCandidateNeedNotBeSelected : DominatedCandidateMustBeSelected → ⊥
dominatedCandidateNeedNotBeSelected ()

selectedRouteDoesNotCreateClaimTruth : SelectedRouteCreatesClaimTruth → ⊥
selectedRouteDoesNotCreateClaimTruth ()

selectedRouteDoesNotCreateSemanticAuthority : SelectedRouteCreatesSemanticAuthority → ⊥
selectedRouteDoesNotCreateSemanticAuthority ()

routeSelectorJsonForbidden : RouteSelectorUsesJson → ⊥
routeSelectorJsonForbidden ()

routeSelectorRegexForbidden : RouteSelectorUsesRegex → ⊥
routeSelectorRegexForbidden ()

mechanismProducerTagAnchor : Nat
mechanismProducerTagAnchor = Producer.producerFamilyTag Producer.mechanismEvidence
