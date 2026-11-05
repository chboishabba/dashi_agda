module DASHI.Cognition.CCDCOEMaxCutRegressionExact where

-- Thin, theorem-level calls to existing owners. No duplicate graph
-- connectivity or PNF-evidence logic. The arbitrary-graph core has its
-- own --safe source; this umbrella imports additional pre-existing owners.

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.CCDCOECognitiveMultiplexInvariantExact as C
import DASHI.Cognition.CCDCOEMultiplexGraphCutCoreExact as G
import DASHI.Cognition.CCDCOEFiveLayerCertifiedCutExact as M
import DASHI.Cognition.CCDCOEQueryPNFEvidenceBridgeExact as Q
import DASHI.Cognition.CCDCOEPersonalHolonomyBoundaryExact as H
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

fullRouteWitness :
  G.Walk (G.NetworkEdge M.fullNetwork)
    (G.node C.agentA C.epistemic)
    (G.node C.agentA C.teleological)
fullRouteWitness = M.fullSpanningWalk C.agentA

allRoutesBlockedAfterCertifiedCut :
  G.Walk (G.NetworkEdge M.cutNetwork)
    (G.node C.agentA C.epistemic)
    (G.node C.agentB C.teleological) →
  G.Void
allRoutesBlockedAfterCertifiedCut =
  M.noCrossCutWalk C.agentA C.agentB

withinLayerStillConnected :
  G.NetworkEdge M.cutNetwork
    (G.node C.agentA C.social)
    (G.node C.agentB C.social)
withinLayerStillConnected =
  M.localLinkSurvivesCut C.social C.agentA C.agentB

visibleQuestionStillAdequate :
  Query.AdequateFor
    Q.outwardEpisode Q.semantics Q.outwardFunctionQuestion
visibleQuestionStillAdequate = Q.functionQueryIsAdequate

unobservedIntegrityQuestionCannotFactor :
  Query.AdequateFor
    Q.outwardEpisode Q.semantics Q.interlayerIntegrityQuestion →
  G.Void
unobservedIntegrityQuestionCannotFactor factor =
  -- Existing query theorem returns Data.Empty. Pattern elimination
  -- builds the local graph core's empty-type certificate.
  let impossibility = Q.outwardCannotAnswerIntegrity factor in
  emptyElim impossibility
  where
    emptyElim : ⊥ → G.Void
    emptyElim ()

humanContextLoopBaseline :
  H.holonomy H.identityConnection H.baselineState ≡ H.baselineState
humanContextLoopBaseline = H.identityLoopPreservesState H.baselineState

humanContextLoopAltered :
  H.holonomy H.revisedConnection H.baselineState ≡ H.revisedState
humanContextLoopAltered = H.revisedLoopChangesSelectedState

