{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact where

------------------------------------------------------------------------
-- ROUND146: LIVE BALABAN SOURCE CUT AS AN ARISTOTLE AND/OR HYPERGRAPH
--
-- Source-semantics correction inspired by live PR #670, without importing it:
-- the direct Round108 route requires BOTH a source-fixed beta-density semantics
-- family and the selected-potential match to BC1.  The fallback route requires
-- BOTH CombinedRG semantic leaves.  Neither child alone inherits whole-route
-- authority.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle

data BalabanFrontierLeaf : Set where
  densityActionRealization
  round108FixedDensitySemantics
  round108SelectedPotentialMatchesBC1
  densityToCombinedRGState
  combinedRGStateToBC1Potential
  physicalCompositeD1ChainRule
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
  round108SemanticsAction
  round108SourceMatchAction
  realizeDensityStateAction
  realizeStatePotentialAction
  physicalD1ChainRuleAction
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
routeSource round108SemanticsAction = round108FixedDensitySemantics
routeSource round108SourceMatchAction = round108SelectedPotentialMatchesBC1
routeSource realizeDensityStateAction = densityToCombinedRGState
routeSource realizeStatePotentialAction = combinedRGStateToBC1Potential
routeSource physicalD1ChainRuleAction = physicalCompositeD1ChainRule
routeSource assembleStressAction = stressInsertionEqualsPhysicalD1Sum
routeSource metricDomainAction = metricPerturbationAdmission
routeSource a1HistoryAction = a1CouplingToBetaHistory
routeSource a2HistoryAction = a2CouplingToBetaHistory
routeSource schwingerEndpointAction = cmp119FiniteMeasureSchwingerEndpoint
routeSource closeUnifiedSectorAction = unifiedSectorStressRecovery

routeTargets : BalabanFrontierRoute → List BalabanFrontierLeaf
routeTargets directRound108ActionRoute =
  round108FixedDensitySemantics ∷ round108SelectedPotentialMatchesBC1 ∷ []
routeTargets viaCombinedRGActionRoute =
  densityToCombinedRGState ∷ combinedRGStateToBC1Potential ∷ []

-- Unresolved source leaves self-block; [] remains reserved for evidence-bearing
-- terminal actions only.
routeTargets round108SemanticsAction = round108FixedDensitySemantics ∷ []
routeTargets round108SourceMatchAction = round108SelectedPotentialMatchesBC1 ∷ []
routeTargets realizeDensityStateAction = densityToCombinedRGState ∷ []
routeTargets realizeStatePotentialAction = combinedRGStateToBC1Potential ∷ []
routeTargets physicalD1ChainRuleAction = physicalCompositeD1ChainRule ∷ []
routeTargets assembleStressAction = stressInsertionEqualsPhysicalD1Sum ∷ []
routeTargets metricDomainAction = metricPerturbationAdmission ∷ []
routeTargets a1HistoryAction = a1CouplingToBetaHistory ∷ []
routeTargets a2HistoryAction = a2CouplingToBetaHistory ∷ []
routeTargets schwingerEndpointAction = cmp119FiniteMeasureSchwingerEndpoint ∷ []

routeTargets closeUnifiedSectorAction =
  densityActionRealization ∷
  physicalCompositeD1ChainRule ∷
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

directRound108RouteTargetsFixedSemanticsAndMatch :
  Aristotle.targets balabanFrontierHypergraph directRound108ActionRoute
  ≡ round108FixedDensitySemantics ∷ round108SelectedPotentialMatchesBC1 ∷ []
directRound108RouteTargetsFixedSemanticsAndMatch = refl

combinedRGRouteTargetsTwoSemanticLeaves :
  Aristotle.targets balabanFrontierHypergraph viaCombinedRGActionRoute
  ≡ densityToCombinedRGState ∷ combinedRGStateToBC1Potential ∷ []
combinedRGRouteTargetsTwoSemanticLeaves = refl

unifiedSectorRouteTargets :
  Aristotle.targets balabanFrontierHypergraph closeUnifiedSectorAction
  ≡ densityActionRealization ∷
    physicalCompositeD1ChainRule ∷
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
