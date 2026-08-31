{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact where

------------------------------------------------------------------------
-- ROUND146: THE LIVE BALABAN SOURCE CUT AS AN ARISTOTLE-STYLE HYPERGRAPH
--
-- Cross-pollination is structural only.  Aristotle's OR-state / AND-action
-- search semantics is reused, but no empirical claim about Aristotle search
-- quality or convergence is imported.
--
-- A frontier state is one exact source obligation remaining after the merged
-- Round132--145 same-action compilation.  A route may split into several
-- prerequisites; closing the route therefore requires ALL target states.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle

-- Exact remaining physical/source coordinates.  These are intentionally more
-- specific than a generic "prove Yang--Mills" state.
data BalabanFrontierLeaf : Set where
  densityToCombinedRGState
  combinedRGStateToBC1Potential
  componentLocalizedD1ToPhysicalD1
  physicalComponentD1SumToStressInsertion
  metricPerturbationAdmission
  a1CouplingToBetaHistory
  a2CouplingToBetaHistory
  cmp119FiniteMeasureSchwingerEndpoint
  unifiedSectorStressRecovery
  : BalabanFrontierLeaf

-- Search actions are decompositions/reuse routes, not theorem evidence.
data BalabanFrontierRoute : Set where
  realizeDensityAction
  realizePotentialAction
  componentD1Action
  assembleStressAction
  metricDomainAction
  a1HistoryAction
  a2HistoryAction
  schwingerEndpointAction
  closeUnifiedSectorAction
  : BalabanFrontierRoute

routeSource : BalabanFrontierRoute → BalabanFrontierLeaf
routeSource realizeDensityAction = densityToCombinedRGState
routeSource realizePotentialAction = combinedRGStateToBC1Potential
routeSource componentD1Action = componentLocalizedD1ToPhysicalD1
routeSource assembleStressAction = physicalComponentD1SumToStressInsertion
routeSource metricDomainAction = metricPerturbationAdmission
routeSource a1HistoryAction = a1CouplingToBetaHistory
routeSource a2HistoryAction = a2CouplingToBetaHistory
routeSource schwingerEndpointAction = cmp119FiniteMeasureSchwingerEndpoint
routeSource closeUnifiedSectorAction = unifiedSectorStressRecovery

-- Most source leaves are irreducible at the current repository cut: their route
-- has no *repository-internal* child theorem yet.  The final sector recovery is
-- different: the merged compiler says it requires the exact same-action/source
-- identities plus metric and Schwinger endpoint evidence.  We expose that AND
-- decomposition literally.
routeTargets : BalabanFrontierRoute → List BalabanFrontierLeaf
routeTargets realizeDensityAction = []
routeTargets realizePotentialAction = []
routeTargets componentD1Action = []
routeTargets assembleStressAction = componentLocalizedD1ToPhysicalD1 ∷ []
routeTargets metricDomainAction = []
routeTargets a1HistoryAction = []
routeTargets a2HistoryAction = []
routeTargets schwingerEndpointAction = []
routeTargets closeUnifiedSectorAction =
  densityToCombinedRGState ∷
  combinedRGStateToBC1Potential ∷
  componentLocalizedD1ToPhysicalD1 ∷
  physicalComponentD1SumToStressInsertion ∷
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

-- This theorem records the useful AND decomposition without claiming any source
-- leaf is actually inhabited.  It is a graph-shape statement, not a physics
-- proof.
unifiedSectorRouteTargets :
  Aristotle.targets balabanFrontierHypergraph closeUnifiedSectorAction
  ≡ densityToCombinedRGState ∷
    combinedRGStateToBC1Potential ∷
    componentLocalizedD1ToPhysicalD1 ∷
    physicalComponentD1SumToStressInsertion ∷
    metricPerturbationAdmission ∷
    a1CouplingToBetaHistory ∷
    a2CouplingToBetaHistory ∷
    cmp119FiniteMeasureSchwingerEndpoint ∷ []
unifiedSectorRouteTargets = Agda.Builtin.Equality.refl

balabanPhysicalFrontierHypergraphLevel : ProofLevel
balabanPhysicalFrontierHypergraphLevel = machineChecked

-- A terminal target list in this search graph means "no further repository
-- decomposition currently installed"; it does NOT manufacture the corresponding
-- physical source proof.  Actual source evidence remains external to this graph.
literalBalabanFrontierLeafInhabitationLevel : ProofLevel
literalBalabanFrontierLeafInhabitationLevel = conditional
