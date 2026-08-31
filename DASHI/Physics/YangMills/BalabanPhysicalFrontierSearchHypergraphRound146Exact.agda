{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact where

------------------------------------------------------------------------
-- ROUND146: THE LIVE BALABAN SOURCE CUT AS AN ARISTOTLE-STYLE HYPERGRAPH
--
-- Cross-pollination is structural only.  Aristotle's OR-state / AND-action
-- search semantics is reused, but no empirical claim about Aristotle search
-- quality or convergence is imported.
--
-- IMPORTANT: in Aristotle's semantics an action with `targets = []` is a
-- successful terminal proof.  Therefore unresolved physical source leaves are
-- deliberately represented by self-blocking routes below.  A future adapter may
-- add a genuinely terminal action only when it carries the exact source proof.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle

-- Exact remaining physical/source coordinates after the merged Round132--145
-- same-action compilation.
data BalabanFrontierLeaf : Set where
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

-- Search actions are route/decomposition proposals, not theorem evidence.
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
routeSource assembleStressAction = stressInsertionEqualsPhysicalD1Sum
routeSource metricDomainAction = metricPerturbationAdmission
routeSource a1HistoryAction = a1CouplingToBetaHistory
routeSource a2HistoryAction = a2CouplingToBetaHistory
routeSource schwingerEndpointAction = cmp119FiniteMeasureSchwingerEndpoint
routeSource closeUnifiedSectorAction = unifiedSectorStressRecovery

-- Self-targeting marks a source leaf as unresolved/nonterminal.  It prevents the
-- raw search graph from manufacturing `ActionProved` through Aristotle's empty-
-- target terminal rule.  The final unified-sector route is the useful AND node.
routeTargets : BalabanFrontierRoute → List BalabanFrontierLeaf
routeTargets realizeDensityAction = densityToCombinedRGState ∷ []
routeTargets realizePotentialAction = combinedRGStateToBC1Potential ∷ []
routeTargets componentD1Action = componentLocalizedD1ToPhysicalD1 ∷ []
routeTargets assembleStressAction = stressInsertionEqualsPhysicalD1Sum ∷ []
routeTargets metricDomainAction = metricPerturbationAdmission ∷ []
routeTargets a1HistoryAction = a1CouplingToBetaHistory ∷ []
routeTargets a2HistoryAction = a2CouplingToBetaHistory ∷ []
routeTargets schwingerEndpointAction = cmp119FiniteMeasureSchwingerEndpoint ∷ []
routeTargets closeUnifiedSectorAction =
  densityToCombinedRGState ∷
  combinedRGStateToBC1Potential ∷
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

unifiedSectorRouteTargets :
  Aristotle.targets balabanFrontierHypergraph closeUnifiedSectorAction
  ≡ densityToCombinedRGState ∷
    combinedRGStateToBC1Potential ∷
    componentLocalizedD1ToPhysicalD1 ∷
    stressInsertionEqualsPhysicalD1Sum ∷
    metricPerturbationAdmission ∷
    a1CouplingToBetaHistory ∷
    a2CouplingToBetaHistory ∷
    cmp119FiniteMeasureSchwingerEndpoint ∷ []
unifiedSectorRouteTargets = refl

-- Explicit regression against the accidental empty-target interpretation.
realizeDensityRouteIsNotTerminal :
  Aristotle.targets balabanFrontierHypergraph realizeDensityAction
  ≡ densityToCombinedRGState ∷ []
realizeDensityRouteIsNotTerminal = refl

balabanPhysicalFrontierHypergraphLevel : ProofLevel
balabanPhysicalFrontierHypergraphLevel = machineChecked

literalBalabanFrontierLeafInhabitationLevel : ProofLevel
literalBalabanFrontierLeafInhabitationLevel = conditional
