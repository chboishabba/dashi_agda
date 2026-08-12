module DASHI.Crypto.ConstraintCouplingSearchExact where

------------------------------------------------------------------------
-- CONSTRAINT COUPLING / SEPARATOR SEARCH
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Explicit coupling graph.  Vertices are local residual coordinates; an edge
-- means the corresponding constraints share information that reconciliation
-- must respect.
------------------------------------------------------------------------

record ConstraintCouplingGraph : Set₁ where
  constructor constraintCouplingGraph
  field
    Vertex : Set
    Coupled : Vertex → Vertex → Set
open ConstraintCouplingGraph public

data Side : Set where leftSide rightSide : Side

record DisconnectedCut (graph : ConstraintCouplingGraph) : Set₁ where
  constructor disconnectedCut
  field
    side : Vertex graph → Side
    noCrossEdge : ∀ {u v} →
      Coupled graph u v →
      side u ≡ side v
open DisconnectedCut public

-- A literal cross-edge refutes a claimed disconnected cut when its endpoints
-- are proved to lie on opposite sides.
record CrossEdgeWitness (graph : ConstraintCouplingGraph) : Set where
  constructor crossEdgeWitness
  field
    u v : Vertex graph
    edge : Coupled graph u v
    differentSides : ∀ (cut : DisconnectedCut graph) →
      side cut u ≡ side cut v → ⊥
open CrossEdgeWitness public

record DisconnectedTwoComponentProblem : Set₁ where
  constructor disconnectedTwoComponentProblem
  field
    Left Right : Set
    ValidL : Left → Set
    ValidR : Right → Set
open DisconnectedTwoComponentProblem public

GlobalDisconnected :
  (problem : DisconnectedTwoComponentProblem) → Left problem × Right problem → Set
GlobalDisconnected problem (l , r) = ValidL problem l × ValidR problem r

disconnectedSearchFactors :
  ∀ {problem : DisconnectedTwoComponentProblem}
    {l : Left problem} {r : Right problem} →
  ValidL problem l → ValidR problem r → GlobalDisconnected problem (l , r)
disconnectedSearchFactors left right = left , right

------------------------------------------------------------------------
-- Connectedness alone is not hardness. Equality couples two Bool variables,
-- yet (false,false) is an immediate satisfying witness.
------------------------------------------------------------------------

data EqualityConstraint : Bool → Bool → Set where
  eq-false : EqualityConstraint false false
  eq-true : EqualityConstraint true true

record ConnectedBoolWitness : Set where
  constructor connectedBoolWitness
  field
    left right : Bool
    edgeConstraint : EqualityConstraint left right

connectedConstraintHasEasyWitness : ConnectedBoolWitness
connectedConstraintHasEasyWitness = connectedBoolWitness false false eq-false

------------------------------------------------------------------------
-- Separator certificate. A full graph-theoretic treewidth theorem is not
-- smuggled in: the application supplies the separator-state count and the
-- conditioned work on each side. This is the exact finite DP seam.
------------------------------------------------------------------------

record BoundedSeparatorSearchCertificate : Set where
  constructor boundedSeparatorSearchCertificate
  field
    separatorStates : Nat
    leftWorkPerState : Nat
    rightWorkPerState : Nat
    reconcileWorkPerState : Nat
open BoundedSeparatorSearchCertificate public

separatorDPBound : BoundedSeparatorSearchCertificate → Nat
separatorDPBound certificate =
  separatorStates certificate *
  (leftWorkPerState certificate +
   rightWorkPerState certificate +
   reconcileWorkPerState certificate)

record WidthBoundedSeparator : Set where
  constructor widthBoundedSeparator
  field
    widthBound : Nat
    stateAlphabetSize : Nat
    suppliedStateBound : Nat
    separatorSearch : BoundedSeparatorSearchCertificate
open WidthBoundedSeparator public

record ReconciliationRestoresBottleneck : Set where
  constructor reconciliationRestoresBottleneck
  field
    rawHiddenWork : Nat
    localWork : Nat
    reconciliationWork : Nat
    combinedWork : Nat
    exactAccounting : combinedWork ≡ localWork + reconciliationWork
open ReconciliationRestoresBottleneck public
