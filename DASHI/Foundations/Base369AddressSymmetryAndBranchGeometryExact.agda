module DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact where

------------------------------------------------------------------------
-- Local operator symmetry and global propagated symmetry are separate.
-- Swapping addresses may commute with the local operator while failing to
-- commute with later propagation because authority, dependency, capacity,
-- or environmental dynamics differ.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import Base369 using (TriTruth)

record AddressTransport
  (Address : Set)
  (Fibre : Address → Set)
  (a b : Address) : Set₁ where
  constructor addressTransport
  field
    forward : Fibre a → Fibre b
    backward : Fibre b → Fibre a
    backwardAfterForward : (x : Fibre a) → backward (forward x) ≡ x
    forwardAfterBackward : (y : Fibre b) → forward (backward y) ≡ y

open AddressTransport public

record AddressedOperator
  (Address : Set)
  (Fibre : Address → Set) : Set₁ where
  constructor addressedOperator
  field
    operate : (a : Address) → Fibre a → Fibre a

open AddressedOperator public

record OperatorEquivariance
  {Address : Set}
  {Fibre : Address → Set}
  (op : AddressedOperator Address Fibre)
  {a b : Address}
  (swap : AddressTransport Address Fibre a b) : Set₁ where
  constructor operatorEquivariance
  field
    commutes :
      (x : Fibre a) →
      forward swap (operate op a x)
      ≡ operate op b (forward swap x)

open OperatorEquivariance public

record AddressedPropagation
  (Address : Set)
  (Fibre : Address → Set) : Set₁ where
  constructor addressedPropagation
  field
    propagate : (a : Address) → Fibre a → Fibre a

open AddressedPropagation public

record PropagationEquivariance
  {Address : Set}
  {Fibre : Address → Set}
  (flow : AddressedPropagation Address Fibre)
  {a b : Address}
  (swap : AddressTransport Address Fibre a b) : Set₁ where
  constructor propagationEquivariance
  field
    commutesThroughTime :
      (x : Fibre a) →
      forward swap (propagate flow a x)
      ≡ propagate flow b (forward swap x)

-- Possessing OperatorEquivariance does not construct PropagationEquivariance.
-- They are intentionally distinct records with no promotion function.

------------------------------------------------------------------------
-- Depth-wise ternary addressing.
------------------------------------------------------------------------

data TritPath : Nat → Set where
  [] : TritPath zero
  _∷_ : {n : Nat} → TriTruth → TritPath n → TritPath (suc n)

infixr 5 _∷_

record SamePrefix {m n : Nat} (short : TritPath m) (long : TritPath n) : Set where
  constructor samePrefix
  field
    witness : TritPath m
    shortExact : witness ≡ short

-- The path is the compact local address.  Rich state, cost, context, phase,
-- and provenance remain in a dependent fibre over that address.
record PathFibre (n : Nat) (Fibre : TritPath n → Set) : Set₁ where
  constructor pathFibre
  field
    path : TritPath n
    payload : Fibre path

------------------------------------------------------------------------
-- Open holes, convergent histories, and constrained strands have different
-- combinatorial geometry.  None is declared to be the unique global carrier.
------------------------------------------------------------------------

record OpenHoleTree (Node Hole : Set) : Set₁ where
  constructor openHoleTree
  field
    root : Node
    holes : Node → Hole → Set
    refine : (node : Node) → (hole : Hole) → holes node hole → Node

record ProvenanceDAG (Node Edge History : Set) : Set₁ where
  constructor provenanceDAG
  field
    source : Edge → Node
    target : Edge → Node
    historyAt : Node → History → Set
    -- Different histories may arrive at the same target node.
    retainHistory : (e : Edge) → History

record ConstrainedBraid (Endpoint Strand Constraint : Set) : Set₁ where
  constructor constrainedBraid
  field
    start : Strand → Endpoint
    finish : Strand → Endpoint
    admissibleCrossing : Strand → Strand → Constraint → Set
    transported : Constraint → Strand → Strand

record BranchGeometry (Tree DAG Braid : Set) : Set where
  constructor branchGeometry
  field
    treePart : Tree
    dagPart : DAG
    braidPart : Braid

------------------------------------------------------------------------
-- Step-state symmetry: nominally different branches may be the same transport
-- orbit at each depth while remaining operationally distinct.
------------------------------------------------------------------------

record StepStateSymmetry
  (Step State : Set)
  (nextA nextB : Step → State → State)
  (rename : State → State) : Set where
  constructor stepStateSymmetry
  field
    stepwiseCommutes :
      (step : Step) →
      (state : State) →
      rename (nextA step state) ≡ nextB step (rename state)

record OperationalMultiplicity (Branch : Set) : Set₁ where
  constructor operationalMultiplicity
  field
    representative : Branch
    nominalCopies : Branch → Set
    sharedFuture : Branch → Branch

-- State symmetry may reduce informational diversity without removing the cost
-- of separately maintaining every nominal branch.
