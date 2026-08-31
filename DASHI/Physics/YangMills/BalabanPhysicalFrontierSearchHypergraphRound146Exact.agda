{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact where

------------------------------------------------------------------------
-- ROUND146: THE LIVE BALABAN SOURCE CUT AS AN ARISTOTLE-STYLE HYPERGRAPH
--
-- Updated after Round108 and Round152 audits.  Density/action realization is an
-- OR state.  The old localized-D1 identity is no longer a source leaf: Round152
-- derives it from Round118 pointwise identity + Round143 congruence once the
-- exact physical composite D1 chain rule is supplied.
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
routeTargets directRound108ActionRoute = round108SelectedPotentialMatchesBC1 ∷ []
routeTargets viaCombinedRGActionRoute =
  densityToCombinedRGState ∷ combinedRGStateToBC1Potential ∷ []

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
