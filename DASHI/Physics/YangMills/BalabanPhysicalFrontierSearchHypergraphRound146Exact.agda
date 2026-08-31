{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact where

------------------------------------------------------------------------
-- ROUND146: THE LIVE BALABAN SOURCE CUT AS AN ARISTOTLE-STYLE HYPERGRAPH
--
-- Updated after the Round108 audit: density->BC1 action realization is an OR
-- state with two genuinely different routes.  One goes directly through the
-- beta-driven localized effective-action family; the other factors through the
-- repository CombinedRG state trajectory.
--
-- Empty-target actions remain reserved for actual evidence-bearing terminal
-- proofs.  Unresolved physical leaves self-block instead.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle

data BalabanFrontierLeaf : Set where
  densityActionRealization
  round108SelectedPotentialMatchesBC1
  densityToCombinedRGState
  combinedRGStateToBC1Potential
  componentLocalizedD1ToPhysicalD1
  stressInsertionEqualsPhysicalD1Sum
  metricPerturbationAdmission
  a1CouplingToBetaHistory
  a2CouplingToBetaHistory
  cmp119FiniteMeasureSchwingerEndpoint
  unifiedSectorStressRecovery
  : BalabanFrontierLeaf

data BalabanFrontierRoute : Set where
  directRound108ActionRoute
  viaCombinedRGActionRoute
  round108SourceMatchAction
  realizeDensityStateAction
  realizeStatePotentialAction
  componentD1Action
  assembleStressAction
  metricDomainAction
  a1HistoryAction
  a2HistoryAction
  schwingerEndpointAction
  closeUnifiedSectorAction
  : BalabanFrontierRoute

routeSource : BalabanFrontierRoute → BalabanFrontierLeaf
routeSource directRound108ActionRoute = densityActionRealization
routeSource viaCombinedRGActionRoute = densityActionRealization
routeSource round108SourceMatchAction = round108SelectedPotentialMatchesBC1
routeSource realizeDensityStateAction = densityToCombinedRGState
routeSource realizeStatePotentialAction = combinedRGStateToBC1Potential
routeSource componentD1Action = componentLocalizedD1ToPhysicalD1
routeSource assembleStressAction = stressInsertionEqualsPhysicalD1Sum
routeSource metricDomainAction = metricPerturbationAdmission
routeSource a1HistoryAction = a1CouplingToBetaHistory
routeSource a2HistoryAction = a2CouplingToBetaHistory
routeSource schwingerEndpointAction = cmp119FiniteMeasureSchwingerEndpoint
routeSource closeUnifiedSectorAction = unifiedSectorStressRecovery

routeTargets : BalabanFrontierRoute → List BalabanFrontierLeaf
-- OR at densityActionRealization:
routeTargets directRound108ActionRoute = round108SelectedPotentialMatchesBC1 ∷ []
routeTargets viaCombinedRGActionRoute =
  densityToCombinedRGState ∷ combinedRGStateToBC1Potential ∷ []

-- Unresolved source leaves are nonterminal/self-blocking.
routeTargets round108SourceMatchAction = round108SelectedPotentialMatchesBC1 ∷ []
routeTargets realizeDensityStateAction = densityToCombinedRGState ∷ []
routeTargets realizeStatePotentialAction = combinedRGStateToBC1Potential ∷ []
routeTargets componentD1Action = componentLocalizedD1ToPhysicalD1 ∷ []
routeTargets assembleStressAction = stressInsertionEqualsPhysicalD1Sum ∷ []
routeTargets metricDomainAction = metricPerturbationAdmission ∷ []
routeTargets a1HistoryAction = a1CouplingToBetaHistory ∷ []
routeTargets a2HistoryAction = a2CouplingToBetaHistory ∷ []
routeTargets schwingerEndpointAction = cmp119FiniteMeasureSchwingerEndpoint ∷ []

-- Final AND node now needs the abstract action-realization state, not both of its
-- alternative constructions simultaneously.
routeTargets closeUnifiedSectorAction =
  densityActionRealization ∷
  componentLocalizedD1ToPhysicalD1 ∷
  stressInsertionEqualsPhysicalD1Sum ∷
  metricPerturbationAdmission ∷
  a1CouplingToBetaHistory ∷
  a2CouplingToBetaHistory ∷
  cmp119FiniteMeasureSchwingerEndpoint ∷ []

balabanFrontierHypergraph : Aristotle.SearchHypergraph
balabanFrontierHypergraph = record
  { Aristotle.SearchHypergraph.State = BalabanFrontierLeaf
  ; Aristotle.SearchHypergraph.Action = BalabanFrontierRoute
  ; Aristotle.SearchHypergraph.source = routeSource
  ; Aristotle.SearchHypergraph.targets = routeTargets
  }

densityActionHasDirectRound108Route :
  Aristotle.source balabanFrontierHypergraph directRound108ActionRoute
  ≡ densityActionRealization
densityActionHasDirectRound108Route = refl

densityActionHasCombinedRGRoute :
  Aristotle.source balabanFrontierHypergraph viaCombinedRGActionRoute
  ≡ densityActionRealization
densityActionHasCombinedRGRoute = refl

directRound108RouteTargetsOnlySourceMatch :
  Aristotle.targets balabanFrontierHypergraph directRound108ActionRoute
  ≡ round108SelectedPotentialMatchesBC1 ∷ []
directRound108RouteTargetsOnlySourceMatch = refl

combinedRGRouteTargetsTwoSemanticLeaves :
  Aristotle.targets balabanFrontierHypergraph viaCombinedRGActionRoute
  ≡ densityToCombinedRGState ∷ combinedRGStateToBC1Potential ∷ []
combinedRGRouteTargetsTwoSemanticLeaves = refl

unifiedSectorRouteTargets :
  Aristotle.targets balabanFrontierHypergraph closeUnifiedSectorAction
  ≡ densityActionRealization ∷
    componentLocalizedD1ToPhysicalD1 ∷
    stressInsertionEqualsPhysicalD1Sum ∷
    metricPerturbationAdmission ∷
    a1CouplingToBetaHistory ∷
    a2CouplingToBetaHistory ∷
    cmp119FiniteMeasureSchwingerEndpoint ∷ []
unifiedSectorRouteTargets = refl

balabanPhysicalFrontierHypergraphLevel : ProofLevel
balabanPhysicalFrontierHypergraphLevel = machineChecked

literalBalabanFrontierLeafInhabitationLevel : ProofLevel
literalBalabanFrontierLeafInhabitationLevel = conditional
