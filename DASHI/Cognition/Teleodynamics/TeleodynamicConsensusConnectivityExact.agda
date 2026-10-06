module DASHI.Cognition.Teleodynamics.TeleodynamicConsensusConnectivityExact where

------------------------------------------------------------------------
-- CONNECTED CONSENSUS: STRUCTURAL ENDPOINT
--
-- This pays the graph-theoretic half of the radiant-coupling consensus route.
-- If a limiting/stationary state agrees across every admitted positive-coupling
-- edge, positive-edge connectivity propagates that equality globally.
--
-- It intentionally does NOT prove that the dynamical flow converges to such a
-- stationary limit.  That remaining analytic convergence receipt is separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- 1. Positive-edge reachability.
------------------------------------------------------------------------

data PositivePath
    (Node : Set)
    (PositiveEdge : Node → Node → Set)
    (root : Node) : Node → Set where
  rootPath : PositivePath Node PositiveEdge root root
  extendPath :
    {u v : Node} →
    PositivePath Node PositiveEdge root u →
    PositiveEdge u v →
    PositivePath Node PositiveEdge root v

PositiveConnectedAt :
  {Node : Set} →
  (PositiveEdge : Node → Node → Set) →
  Node →
  Set
PositiveConnectedAt {Node} PositiveEdge root =
  (node : Node) → PositivePath Node PositiveEdge root node

EdgeAgreement :
  {Node State : Set} →
  (PositiveEdge : Node → Node → Set) →
  (state : Node → State) →
  Set
EdgeAgreement {Node} PositiveEdge state =
  (i j : Node) → PositiveEdge i j → state i ≡ state j

------------------------------------------------------------------------
-- 2. Equality propagates along a positive path.
------------------------------------------------------------------------

positivePathPropagatesAgreement :
  ∀ {Node State : Set}
    {PositiveEdge : Node → Node → Set}
    {state : Node → State}
    {root node : Node} →
  PositivePath Node PositiveEdge root node →
  EdgeAgreement PositiveEdge state →
  state root ≡ state node
positivePathPropagatesAgreement rootPath edgeAgreement = refl
positivePathPropagatesAgreement
  (extendPath {u = u} {v = v} prior edge)
  edgeAgreement =
  trans
    (positivePathPropagatesAgreement prior edgeAgreement)
    (edgeAgreement u v edge)

connectedEdgewiseAgreementImpliesConsensus :
  ∀ {Node State : Set}
    {PositiveEdge : Node → Node → Set}
    {state : Node → State}
    {root : Node} →
  PositiveConnectedAt PositiveEdge root →
  EdgeAgreement PositiveEdge state →
  (node : Node) →
  state node ≡ state root
connectedEdgewiseAgreementImpliesConsensus connected edgeAgreement node =
  sym (positivePathPropagatesAgreement (connected node) edgeAgreement)

------------------------------------------------------------------------
-- 3. Exact remaining analytic seam.
------------------------------------------------------------------------

record ConsensusLimitReceipt (Node State : Set) : Set₁ where
  constructor consensus-limit-receipt
  field
    PositiveEdge : Node → Node → Set
    root : Node
    limitState : Node → State
    positiveConnected : PositiveConnectedAt PositiveEdge root
    edgewiseStationaryAgreement : EdgeAgreement PositiveEdge limitState
    FlowConvergenceReceipt : Set
    flowConvergenceReceipt : FlowConvergenceReceipt

open ConsensusLimitReceipt public

consensusLimitReceiptGivesPairwiseConsensus :
  ∀ {Node State : Set} →
  (receipt : ConsensusLimitReceipt Node State) →
  (i j : Node) →
  limitState receipt i ≡ limitState receipt j
consensusLimitReceiptGivesPairwiseConsensus receipt i j =
  trans
    (connectedEdgewiseAgreementImpliesConsensus
      (positiveConnected receipt)
      (edgewiseStationaryAgreement receipt)
      i)
    (sym
      (connectedEdgewiseAgreementImpliesConsensus
        (positiveConnected receipt)
        (edgewiseStationaryAgreement receipt)
        j))

------------------------------------------------------------------------
-- 4. Authority boundary.
------------------------------------------------------------------------

record TeleodynamicConsensusConnectivityBoundary : Set where
  constructor teleodynamic-consensus-connectivity-boundary
  field
    positiveEdgeReachabilityTyped : Bool
    connectedStationaryStateIsConsensus : Bool
    convergenceReceiptSeparated : Bool
    connectivityAloneProvesFlowConvergence : Bool
    consensusCreatesNonlocalTransmission : Bool

open TeleodynamicConsensusConnectivityBoundary public

canonicalConsensusConnectivityBoundary :
  TeleodynamicConsensusConnectivityBoundary
canonicalConsensusConnectivityBoundary =
  teleodynamic-consensus-connectivity-boundary
    true true true false false
