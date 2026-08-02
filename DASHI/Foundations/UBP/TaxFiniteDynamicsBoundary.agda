module DASHI.Foundations.UBP.TaxFiniteDynamicsBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.LeechValidMoveSet as Moves

data TaxEdgeDelta : Set where
  taxDecreases : TaxEdgeDelta
  taxConstant : TaxEdgeDelta
  taxIncreases : TaxEdgeDelta

record FiniteTransitionGraph : Set₁ where
  field
    State : Set
    states : List State
    edge : State → State → Bool
    taxDelta : State → State → TaxEdgeDelta
    edgeClassificationTotal :
      (from to : State) →
      edge from to ≡ true →
      Set

open FiniteTransitionGraph public

data DirectedPath
    (graph : FiniteTransitionGraph) :
    State graph → State graph → Set where
  emptyPath :
    (state : State graph) →
    DirectedPath graph state state
  edgePath :
    (from to : State graph) →
    edge graph from to ≡ true →
    DirectedPath graph from to
  composePath :
    ∀ {from middle to} →
    DirectedPath graph from middle →
    DirectedPath graph middle to →
    DirectedPath graph from to

record StronglyConnectedComponent
    (graph : FiniteTransitionGraph) : Set₁ where
  field
    contains : State graph → Set
    nonempty : Set
    mutuallyReachable :
      (left right : State graph) →
      contains left →
      contains right →
      DirectedPath graph left right
    maximal : Set

open StronglyConnectedComponent public

record TaxLyapunovDecomposition
    (graph : FiniteTransitionGraph) : Set₁ where
  field
    components : List (StronglyConnectedComponent graph)
    everyStateAssigned : Set
    quotientEdge : StronglyConnectedComponent graph →
      StronglyConnectedComponent graph → Bool
    quotientAcyclic : Set
    recurrentComponentsTaxConstant : Set
    interComponentEdgesStrictlyDecrease : Set
    positiveTaxEdgeInsideCertifiedGraphExists : Bool
    noPositiveTaxEdgeClaim :
      positiveTaxEdgeInsideCertifiedGraphExists ≡ false

open TaxLyapunovDecomposition public

record CertifiedLeechTransitionInstantiation : Set₁ where
  field
    lattice : Moves.AdditiveLattice
    graph : FiniteTransitionGraph
    stateIsLatticePoint :
      State graph → Moves.Point lattice
    everyGraphEdgeHasCertifiedMove : Set
    finiteStateCoverage : Set
    taxObservableDefinedOnStates : Set
    decomposition : TaxLyapunovDecomposition graph

open CertifiedLeechTransitionInstantiation public

record TaxDynamicsStatus : Set where
  constructor taxDynamicsStatus
  field
    frameworkAuthors : String
    frameworkTitle : String
    frameworkDOI : String
    certifiedTransitionGraphInterfaceSupplied : Bool
    certifiedTransitionGraphInterfaceSuppliedIsTrue :
      certifiedTransitionGraphInterfaceSupplied ≡ true
    SCCDecompositionRequiredBeforeLyapunovPromotion : Bool
    SCCDecompositionRequiredBeforeLyapunovPromotionIsTrue :
      SCCDecompositionRequiredBeforeLyapunovPromotion ≡ true
    exactEdgeSignPartitionRequired : Bool
    exactEdgeSignPartitionRequiredIsTrue :
      exactEdgeSignPartitionRequired ≡ true
    concreteLeechGraphInstantiated : Bool
    concreteLeechGraphInstantiatedIsFalse :
      concreteLeechGraphInstantiated ≡ false
    TAXIsCompleteLyapunovFunctionEstablished : Bool
    TAXIsCompleteLyapunovFunctionEstablishedIsFalse :
      TAXIsCompleteLyapunovFunctionEstablished ≡ false
    continuousNumericalCollocationRequiredForFirstFiniteModel : Bool
    continuousNumericalCollocationRequiredForFirstFiniteModelIsFalse :
      continuousNumericalCollocationRequiredForFirstFiniteModel ≡ false
    reading : String

canonicalTaxDynamicsStatus : TaxDynamicsStatus
canonicalTaxDynamicsStatus =
  taxDynamicsStatus
    "Peter Giesl, Zachary Langhorne, Carlos Argáez, and Sigurdur Hafstein"
    "Computing complete Lyapunov functions for discrete-time dynamical systems"
    "10.3934/dcdsb.2020331"
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "instantiate certified lattice-valid moves first; then classify TAX edge deltas and compute SCCs before asking for a strict or complete Lyapunov theorem"

taxFiniteDynamicsReceipt : GenericReceipt.GenericReceipt
taxFiniteDynamicsReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "finite TAX transition/SCC/Lyapunov boundary"
    "DASHI.Foundations.UBP.TaxFiniteDynamicsBoundary"
    "canonicalTaxDynamicsStatus"
    "finite certified transition graphs, exact TAX edge-sign classes, directed paths, strongly connected components and a decreasing quotient-DAG certificate are exposed"
    "no concrete Leech graph, SCC computation, TAX monotonicity or complete Lyapunov theorem is claimed before the move system is instantiated"
    "agda -i . DASHI/Foundations/UBP/TaxFiniteDynamicsBoundary.agda"

taxFiniteDynamicsReceiptNonPromoting :
  GenericReceipt.promotesClaim taxFiniteDynamicsReceipt ≡ false
taxFiniteDynamicsReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse taxFiniteDynamicsReceipt
