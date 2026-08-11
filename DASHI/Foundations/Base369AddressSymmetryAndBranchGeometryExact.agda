module DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact where

------------------------------------------------------------------------
-- MATHEMATICAL BACKGROUND
--
-- Emil Artin, "Theory of Braids", Annals of Mathematics 48 (1947),
-- 101--126. DOI: 10.2307/1969218.
--
-- Jean-Pierre Serre, "A Course in Arithmetic", Graduate Texts in
-- Mathematics 7, Springer. DOI: 10.1007/978-1-4684-9884-4.
--
-- DASHI CONTRIBUTION
--
-- Local operator symmetry and global propagated symmetry are separate.
-- Swapping addresses may commute with the local operator while failing to
-- commute with later propagation because authority, dependency, capacity,
-- or environmental dynamics differ.  Depth-wise balanced-ternary paths give
-- finite 3-adic-style prefix addresses.  Open refinement, convergent histories,
-- and constrained transport are represented respectively by tree, DAG, and
-- braid carriers; the concrete three-strand swap operators below satisfy the
-- Artin braid relation by computation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import Base369 using
  ( TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  )

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

-- The path is the compact local address. Rich state, cost, context, phase,
-- and provenance remain in a dependent fibre over that address.
record PathFibre (n : Nat) (Fibre : TritPath n → Set) : Set₁ where
  constructor pathFibre
  field
    path : TritPath n
    payload : Fibre path

------------------------------------------------------------------------
-- Exact finite prefix depth.  This is the discrete exponent underlying the
-- usual 3-adic-style statement that paths sharing a longer prefix are closer.
------------------------------------------------------------------------

tritEqual : TriTruth → TriTruth → Bool
tritEqual tri-low tri-low = true
tritEqual tri-low tri-mid = false
tritEqual tri-low tri-high = false
tritEqual tri-mid tri-low = false
tritEqual tri-mid tri-mid = true
tritEqual tri-mid tri-high = false
tritEqual tri-high tri-low = false
tritEqual tri-high tri-mid = false
tritEqual tri-high tri-high = true

sharedPrefixDepth : {n : Nat} → TritPath n → TritPath n → Nat
sharedPrefixDepth [] [] = zero
sharedPrefixDepth (tri-low ∷ xs) (tri-low ∷ ys) = suc (sharedPrefixDepth xs ys)
sharedPrefixDepth (tri-low ∷ xs) (tri-mid ∷ ys) = zero
sharedPrefixDepth (tri-low ∷ xs) (tri-high ∷ ys) = zero
sharedPrefixDepth (tri-mid ∷ xs) (tri-low ∷ ys) = zero
sharedPrefixDepth (tri-mid ∷ xs) (tri-mid ∷ ys) = suc (sharedPrefixDepth xs ys)
sharedPrefixDepth (tri-mid ∷ xs) (tri-high ∷ ys) = zero
sharedPrefixDepth (tri-high ∷ xs) (tri-low ∷ ys) = zero
sharedPrefixDepth (tri-high ∷ xs) (tri-mid ∷ ys) = zero
sharedPrefixDepth (tri-high ∷ xs) (tri-high ∷ ys) = suc (sharedPrefixDepth xs ys)

sharedPrefixDepthSelf :
  {n : Nat} → (address : TritPath n) → sharedPrefixDepth address address ≡ n
sharedPrefixDepthSelf [] = refl
sharedPrefixDepthSelf (tri-low ∷ xs) rewrite sharedPrefixDepthSelf xs = refl
sharedPrefixDepthSelf (tri-mid ∷ xs) rewrite sharedPrefixDepthSelf xs = refl
sharedPrefixDepthSelf (tri-high ∷ xs) rewrite sharedPrefixDepthSelf xs = refl

-- Two equal trit signatures are only equal symbolic addresses.  No theorem in
-- this module identifies their dependent fibres.

------------------------------------------------------------------------
-- Open holes, convergent histories, and constrained strands have different
-- combinatorial geometry. None is declared to be the unique global carrier.
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
-- A concrete braid: adjacent swaps on a three-strand carrier satisfy
-- sigma_1 sigma_2 sigma_1 = sigma_2 sigma_1 sigma_2 exactly.
------------------------------------------------------------------------

record Triple (A : Set) : Set where
  constructor triple
  field
    first : A
    second : A
    third : A

open Triple public

sigma₁ : {A : Set} → Triple A → Triple A
sigma₁ (triple a b c) = triple b a c

sigma₂ : {A : Set} → Triple A → Triple A
sigma₂ (triple a b c) = triple a c b

sigma₁Involutive : {A : Set} → (x : Triple A) → sigma₁ (sigma₁ x) ≡ x
sigma₁Involutive (triple a b c) = refl

sigma₂Involutive : {A : Set} → (x : Triple A) → sigma₂ (sigma₂ x) ≡ x
sigma₂Involutive (triple a b c) = refl

threeStrandBraidRelation :
  {A : Set} → (x : Triple A) →
  sigma₁ (sigma₂ (sigma₁ x)) ≡ sigma₂ (sigma₁ (sigma₂ x))
threeStrandBraidRelation (triple a b c) = refl

------------------------------------------------------------------------
-- A concrete convergent DAG.  The two distinct middle histories arrive at the
-- same join node, and every edge strictly advances the explicit rank by one.
------------------------------------------------------------------------

data DiamondNode : Set where
  diamondRoot
  diamondLeft
  diamondRight
  diamondJoin : DiamondNode

data DiamondEdge : Set where
  rootToLeft
  rootToRight
  leftToJoin
  rightToJoin : DiamondEdge

diamondSource : DiamondEdge → DiamondNode
diamondSource rootToLeft = diamondRoot
diamondSource rootToRight = diamondRoot
diamondSource leftToJoin = diamondLeft
diamondSource rightToJoin = diamondRight

diamondTarget : DiamondEdge → DiamondNode
diamondTarget rootToLeft = diamondLeft
diamondTarget rootToRight = diamondRight
diamondTarget leftToJoin = diamondJoin
diamondTarget rightToJoin = diamondJoin

diamondRank : DiamondNode → Nat
diamondRank diamondRoot = zero
diamondRank diamondLeft = suc zero
diamondRank diamondRight = suc zero
diamondRank diamondJoin = suc (suc zero)

diamondEdgeAdvancesRank :
  (edge : DiamondEdge) →
  diamondRank (diamondTarget edge) ≡ suc (diamondRank (diamondSource edge))
diamondEdgeAdvancesRank rootToLeft = refl
diamondEdgeAdvancesRank rootToRight = refl
diamondEdgeAdvancesRank leftToJoin = refl
diamondEdgeAdvancesRank rightToJoin = refl

distinctHistoriesConverge :
  diamondTarget leftToJoin ≡ diamondTarget rightToJoin
distinctHistoriesConverge = refl

------------------------------------------------------------------------
-- Local role-swap symmetry with explicit propagated asymmetry.
------------------------------------------------------------------------

record PairState : Set where
  constructor pairState
  field
    leftState : TriTruth
    rightState : TriTruth

open PairState public

swapPair : PairState → PairState
swapPair (pairState a b) = pairState b a

swapPairInvolutive : (x : PairState) → swapPair (swapPair x) ≡ x
swapPairInvolutive (pairState a b) = refl

negateTrit : TriTruth → TriTruth
negateTrit tri-low = tri-high
negateTrit tri-mid = tri-mid
negateTrit tri-high = tri-low

negatePair : PairState → PairState
negatePair (pairState a b) = pairState (negateTrit a) (negateTrit b)

localSwapEquivariance :
  (x : PairState) → swapPair (negatePair x) ≡ negatePair (swapPair x)
localSwapEquivariance (pairState a b) = refl

data ParticipantRole : Set where
  roleA
  roleB : ParticipantRole

contextualPropagate : ParticipantRole → PairState → PairState
contextualPropagate roleA x = x
contextualPropagate roleB (pairState a b) = pairState (negateTrit a) b

asymmetryWitness : PairState
asymmetryWitness = pairState tri-high tri-low

propagateThenSwapAtA :
  swapPair (contextualPropagate roleA asymmetryWitness)
  ≡ pairState tri-low tri-high
propagateThenSwapAtA = refl

swapThenPropagateAtB :
  contextualPropagate roleB (swapPair asymmetryWitness)
  ≡ pairState tri-high tri-high
swapThenPropagateAtB = refl

data Empty : Set where

propagatedSymmetryBrokenAtWitness :
  swapPair (contextualPropagate roleA asymmetryWitness)
  ≡ contextualPropagate roleB (swapPair asymmetryWitness) → Empty
propagatedSymmetryBrokenAtWitness ()

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
