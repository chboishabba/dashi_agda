module DASHI.Foundations.Base369StepStateSymmetryQuotientExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Exact step-state symmetry is stronger than sharing a terminal basin or a
-- bare ternary itinerary.  An enhanced step state retains orientation, refined
-- zero, liveness, servicing cost, attractor drift and boundary status.  This
-- module gives an exact trajectory equivalence, a computable discrepancy, and
-- a concrete time-local quotient whose classes can merge and later split.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import Base369 using
  ( TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  )
open import DASHI.Foundations.Base369SignedMembershipExact using
  ( ZeroKind
  ; zeroUnknown
  ; zeroUnclassified
  ; zeroBalanced
  ; zeroIncomparable
  ; zeroOpen
  ; zeroExpired
  ; zeroCompletedNeutral
  )

------------------------------------------------------------------------
-- Enhanced signatures.
------------------------------------------------------------------------

data BranchBoundary : Set where
  boundaryClosed
  boundaryOpen
  boundaryDeferred
  boundaryExpired : BranchBoundary

record EnhancedStepState : Set where
  constructor enhancedStepState
  field
    orientation : TriTruth
    refinedZero : ZeroKind
    live : Bool
    servicingCost : Nat
    attractorDrift : TriTruth
    boundary : BranchBoundary

open EnhancedStepState public

record ExactStepCorrespondence
  (left right : EnhancedStepState) : Set where
  constructor exactStepCorrespondence
  field
    sameOrientation : orientation left ≡ orientation right
    sameZero : refinedZero left ≡ refinedZero right
    sameLiveness : live left ≡ live right
    sameCost : servicingCost left ≡ servicingCost right
    sameDrift : attractorDrift left ≡ attractorDrift right
    sameBoundary : boundary left ≡ boundary right

open ExactStepCorrespondence public

exactStepCorrespondenceRefl :
  (state : EnhancedStepState) → ExactStepCorrespondence state state
exactStepCorrespondenceRefl state =
  exactStepCorrespondence refl refl refl refl refl refl

------------------------------------------------------------------------
-- Indexed trajectories and exact stepwise equivalence.
------------------------------------------------------------------------

data EnhancedTrajectory : Nat → Set where
  [] : EnhancedTrajectory zero
  _∷_ : {n : Nat} → EnhancedStepState → EnhancedTrajectory n → EnhancedTrajectory (suc n)

infixr 5 _∷_

data StepwiseEquivalent :
  {n : Nat} → EnhancedTrajectory n → EnhancedTrajectory n → Set where
  equivalentEmpty : StepwiseEquivalent [] []
  equivalentStep :
    {n : Nat}
    {leftState rightState : EnhancedStepState}
    {leftTail rightTail : EnhancedTrajectory n} →
    ExactStepCorrespondence leftState rightState →
    StepwiseEquivalent leftTail rightTail →
    StepwiseEquivalent
      (leftState ∷ leftTail)
      (rightState ∷ rightTail)

stepwiseEquivalentRefl :
  {n : Nat} → (trajectory : EnhancedTrajectory n) →
  StepwiseEquivalent trajectory trajectory
stepwiseEquivalentRefl [] = equivalentEmpty
stepwiseEquivalentRefl (state ∷ tail) =
  equivalentStep
    (exactStepCorrespondenceRefl state)
    (stepwiseEquivalentRefl tail)

------------------------------------------------------------------------
-- A computable step discrepancy.  This is the exact finite analogue of the
-- weighted per-step discrepancy used before applying any real-valued kernel.
------------------------------------------------------------------------

tritMismatch : TriTruth → TriTruth → Nat
tritMismatch tri-low tri-low = 0
tritMismatch tri-low tri-mid = 1
tritMismatch tri-low tri-high = 1
tritMismatch tri-mid tri-low = 1
tritMismatch tri-mid tri-mid = 0
tritMismatch tri-mid tri-high = 1
tritMismatch tri-high tri-low = 1
tritMismatch tri-high tri-mid = 1
tritMismatch tri-high tri-high = 0

tritMismatchSelf : (x : TriTruth) → tritMismatch x x ≡ 0
tritMismatchSelf tri-low = refl
tritMismatchSelf tri-mid = refl
tritMismatchSelf tri-high = refl

boolMismatch : Bool → Bool → Nat
boolMismatch false false = 0
boolMismatch false true = 1
boolMismatch true false = 1
boolMismatch true true = 0

boolMismatchSelf : (x : Bool) → boolMismatch x x ≡ 0
boolMismatchSelf false = refl
boolMismatchSelf true = refl

zeroKindMismatch : ZeroKind → ZeroKind → Nat
zeroKindMismatch zeroUnknown zeroUnknown = 0
zeroKindMismatch zeroUnclassified zeroUnclassified = 0
zeroKindMismatch zeroBalanced zeroBalanced = 0
zeroKindMismatch zeroIncomparable zeroIncomparable = 0
zeroKindMismatch zeroOpen zeroOpen = 0
zeroKindMismatch zeroExpired zeroExpired = 0
zeroKindMismatch zeroCompletedNeutral zeroCompletedNeutral = 0
zeroKindMismatch _ _ = 1

zeroKindMismatchSelf : (x : ZeroKind) → zeroKindMismatch x x ≡ 0
zeroKindMismatchSelf zeroUnknown = refl
zeroKindMismatchSelf zeroUnclassified = refl
zeroKindMismatchSelf zeroBalanced = refl
zeroKindMismatchSelf zeroIncomparable = refl
zeroKindMismatchSelf zeroOpen = refl
zeroKindMismatchSelf zeroExpired = refl
zeroKindMismatchSelf zeroCompletedNeutral = refl

boundaryMismatch : BranchBoundary → BranchBoundary → Nat
boundaryMismatch boundaryClosed boundaryClosed = 0
boundaryMismatch boundaryOpen boundaryOpen = 0
boundaryMismatch boundaryDeferred boundaryDeferred = 0
boundaryMismatch boundaryExpired boundaryExpired = 0
boundaryMismatch _ _ = 1

boundaryMismatchSelf : (x : BranchBoundary) → boundaryMismatch x x ≡ 0
boundaryMismatchSelf boundaryClosed = refl
boundaryMismatchSelf boundaryOpen = refl
boundaryMismatchSelf boundaryDeferred = refl
boundaryMismatchSelf boundaryExpired = refl

natMismatch : Nat → Nat → Nat
natMismatch zero zero = 0
natMismatch zero (suc n) = 1
natMismatch (suc n) zero = 1
natMismatch (suc n) (suc m) = natMismatch n m

natMismatchSelf : (n : Nat) → natMismatch n n ≡ 0
natMismatchSelf zero = refl
natMismatchSelf (suc n) = natMismatchSelf n

stepDiscrepancy : EnhancedStepState → EnhancedStepState → Nat
stepDiscrepancy left right =
  tritMismatch (orientation left) (orientation right)
  + zeroKindMismatch (refinedZero left) (refinedZero right)
  + boolMismatch (live left) (live right)
  + natMismatch (servicingCost left) (servicingCost right)
  + tritMismatch (attractorDrift left) (attractorDrift right)
  + boundaryMismatch (boundary left) (boundary right)

stepDiscrepancySelf :
  (state : EnhancedStepState) → stepDiscrepancy state state ≡ 0
stepDiscrepancySelf
  (enhancedStepState orientation zero live cost drift boundary)
  rewrite tritMismatchSelf orientation
        | zeroKindMismatchSelf zero
        | boolMismatchSelf live
        | natMismatchSelf cost
        | tritMismatchSelf drift
        | boundaryMismatchSelf boundary
  = refl

trajectoryDiscrepancy :
  {n : Nat} → EnhancedTrajectory n → EnhancedTrajectory n → Nat
trajectoryDiscrepancy [] [] = 0
trajectoryDiscrepancy (left ∷ leftTail) (right ∷ rightTail) =
  stepDiscrepancy left right
  + trajectoryDiscrepancy leftTail rightTail

trajectoryDiscrepancySelf :
  {n : Nat} → (trajectory : EnhancedTrajectory n) →
  trajectoryDiscrepancy trajectory trajectory ≡ 0
trajectoryDiscrepancySelf [] = refl
trajectoryDiscrepancySelf (state ∷ tail)
  rewrite stepDiscrepancySelf state
        | trajectoryDiscrepancySelf tail
  = refl

------------------------------------------------------------------------
-- Bare trit itinerary equality is weaker than enhanced correspondence.
------------------------------------------------------------------------

data TritTrajectory : Nat → Set where
  tritNil : TritTrajectory zero
  tritCons : {n : Nat} → TriTruth → TritTrajectory n → TritTrajectory (suc n)

projectTritTrajectory :
  {n : Nat} → EnhancedTrajectory n → TritTrajectory n
projectTritTrajectory [] = tritNil
projectTritTrajectory (state ∷ tail) =
  tritCons (orientation state) (projectTritTrajectory tail)

sameTritDifferentCostLeft : EnhancedStepState
sameTritDifferentCostLeft =
  enhancedStepState tri-high zeroBalanced true 1 tri-high boundaryOpen

sameTritDifferentCostRight : EnhancedStepState
sameTritDifferentCostRight =
  enhancedStepState tri-high zeroBalanced true 2 tri-high boundaryOpen

sameTritDifferentCostProjection :
  projectTritTrajectory (sameTritDifferentCostLeft ∷ [])
  ≡ projectTritTrajectory (sameTritDifferentCostRight ∷ [])
sameTritDifferentCostProjection = refl

sameTritDifferentCostHasDiscrepancy :
  trajectoryDiscrepancy
    (sameTritDifferentCostLeft ∷ [])
    (sameTritDifferentCostRight ∷ [])
  ≡ 1
sameTritDifferentCostHasDiscrepancy = refl

------------------------------------------------------------------------
-- Time-local quotient geometry: two histories can be one class now and split
-- later when a contextual perturbation becomes relevant.
------------------------------------------------------------------------

data NominalBranch : Set where
  branchA
  branchB : NominalBranch

data CoarseOrbit : Set where
  sharedOrbit : CoarseOrbit

data RefinedOrbit : Set where
  orbitA
  orbitB : RefinedOrbit

coarseOrbit : NominalBranch → CoarseOrbit
coarseOrbit branchA = sharedOrbit
coarseOrbit branchB = sharedOrbit

refinedOrbit : NominalBranch → RefinedOrbit
refinedOrbit branchA = orbitA
refinedOrbit branchB = orbitB

coarseBranchesMerged : coarseOrbit branchA ≡ coarseOrbit branchB
coarseBranchesMerged = refl

data Empty : Set where

refinedBranchesSplit : refinedOrbit branchA ≡ refinedOrbit branchB → Empty
refinedBranchesSplit ()

------------------------------------------------------------------------
-- Effective diversity and operational multiplicity are separate observables.
------------------------------------------------------------------------

effectiveOrbitCountAtCoarseStep : Nat
effectiveOrbitCountAtCoarseStep = 1

nominalOperationalCopyCount : Nat
nominalOperationalCopyCount = 2

effectiveOrbitCountAtCoarseStepIs1 : effectiveOrbitCountAtCoarseStep ≡ 1
effectiveOrbitCountAtCoarseStepIs1 = refl

nominalOperationalCopyCountIs2 : nominalOperationalCopyCount ≡ 2
nominalOperationalCopyCountIs2 = refl
