module DASHI.Analysis.RiemannDistanceStratifiedObserverIntrospectiveExact where

------------------------------------------------------------------------
-- INTROSPECTIVE ROUND-TRIP: WHY THE HERMITIAN OBSERVER IS FINER
--
-- Calibration:
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), DOI 10.48550/arXiv.2608.13637.
--
-- Starting implemented facts:
--
-- * the source inertia observer assigns every non-fixed reflection pair the
--   same coarse signature code;
-- * the reflection-orbit model retains a nonnegative squared defect;
-- * the source signature cannot reconstruct that squared defect.
--
-- A deterministic comparison visualization placed the SAME reflection pairs
-- through both observers.  Inspection exposed two distinct statements which
-- must not be conflated:
--
-- (1) EXACT INFORMATION ORDER:
--     squared defect refines the binary source signature.  The signature is
--     recovered by asking only whether defect is zero, but the converse
--     factorization was already refuted by near/far collision.
--
-- (2) OPERATIONAL ERROR-BUDGET ORDER:
--     once a nonzero arithmetic error floor is introduced, positive defects
--     below that floor can remain unresolved.  Increasing a distance threshold
--     increases the minimum per-pair defect cost, producing a NESTED FAMILY of
--     admissible pair populations.  This is a distance-stratified strengthening
--     of one distance-blind pair ceiling, not a claim that inertia is useless.
--
-- The visualization is observer-only.  Every result below is re-proved from
-- the existing discrete reflection model and Nat budget algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
import Data.Nat.Solver as NatSolver
open NatSolver.+-*-Solver using ()
  renaming
    ( solve to solveℕ
    ; _:*_ to _:*ℕ_
    ; _:+_ to _:+ℕ_
    ; con to conℕ
    ; _:=_ to _:=ℕ_
    )

import DASHI.Analysis.RiemannReflectionOrbitDefectExact as Orbit
import DASHI.Analysis.RiemannWeilOffLineHyperbolicBlockExact as Inertia

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

------------------------------------------------------------------------
-- FINDING 1: EXACT OBSERVER REFINEMENT
--
-- Collapse a distance-sensitive defect to the published coarse question:
-- zero defect = fixed/critical; any positive defect = non-fixed pair.
------------------------------------------------------------------------

collapseSquaredDefectToSignature : Nat → Nat
collapseSquaredDefectToSignature zero = zero
collapseSquaredDefectToSignature (suc _) = 1

sourceSignatureFactorsThroughSquaredDefect :
  (x : Orbit.CentredReflectionState) →
  collapseSquaredDefectToSignature (Orbit.squaredDefect x)
    ≡ Inertia.sourceSignatureCode x
sourceSignatureFactorsThroughSquaredDefect Orbit.criticalCentre = refl
sourceSignatureFactorsThroughSquaredDefect (Orbit.offLine Orbit.left n) = refl
sourceSignatureFactorsThroughSquaredDefect (Orbit.offLine Orbit.right n) = refl

------------------------------------------------------------------------
-- Strictness is already witnessed by the implemented near/far collision:
--
--   sourceSignatureCode near = sourceSignatureCode far
--   squaredDefect near = 1
--   squaredDefect far  = 9.
--
-- Therefore the factorization exists in only one direction.
------------------------------------------------------------------------

record ExactObserverStrictRefinement : Set where
  constructor exactObserverStrictRefinement
  field
    coarseFromDefect :
      (x : Orbit.CentredReflectionState) →
      collapseSquaredDefectToSignature (Orbit.squaredDefect x)
        ≡ Inertia.sourceSignatureCode x
    coarseCollision :
      Inertia.sourceSignatureCode Inertia.nearOrbit
        ≡ Inertia.sourceSignatureCode Inertia.farOrbit
    fineNearDefect : Orbit.squaredDefect Inertia.nearOrbit ≡ 1
    fineFarDefect : Orbit.squaredDefect Inertia.farOrbit ≡ 9
    noCoarseDecoderForFineDefect :
      (decode : Nat → Nat) →
      ((x : Orbit.CentredReflectionState) →
        decode (Inertia.sourceSignatureCode x) ≡ Orbit.squaredDefect x) →
      ⊥

exactDefectStrictlyRefinesSourceSignature : ExactObserverStrictRefinement
exactDefectStrictlyRefinesSourceSignature =
  exactObserverStrictRefinement
    sourceSignatureFactorsThroughSquaredDefect
    Inertia.nearFarSourceSignatureCollide
    Inertia.nearOrbitDefectIsOne
    Inertia.farOrbitDefectIsNine
    Inertia.sourceSignatureCannotDetermineSquaredDefect

------------------------------------------------------------------------
-- FINDING 2: DISTANCE-STRATIFIED ERROR-BUDGET CEILINGS
--
-- `BudgetFit n f E` means n pairs, each charged at least the threshold floor f,
-- can fit in arithmetic budget E, with explicit nonnegative slack:
--
--   E = n*f + slack.
--
-- Raising the distance threshold raises the per-pair floor.  If the stronger
-- threshold still fits, then the weaker threshold necessarily fits as well.
-- Thus admissible pair populations form nested sets as distance increases.
------------------------------------------------------------------------

record BudgetFit (pairCount defectFloor arithmeticBudget : Nat) : Set where
  constructor budgetFit
  field
    slack : Nat
    budgetDecomposition :
      arithmeticBudget ≡ pairCount * defectFloor + slack

open BudgetFit public

record DefectFloorStrengthening (lowFloor highFloor : Nat) : Set where
  constructor defectFloorStrengthening
  field
    increment : Nat
    highIsLowPlusIncrement : highFloor ≡ lowFloor + increment

open DefectFloorStrengthening public

populationCostDistributesOverFloorIncrease :
  (n low inc slack : Nat) →
  n * (low + inc) + slack
    ≡ n * low + (n * inc + slack)
populationCostDistributesOverFloorIncrease n low inc slack =
  solveℕ 4
    (λ n low inc slack →
      (n :*ℕ (low :+ℕ inc)) :+ℕ slack
        :=ℕ (n :*ℕ low) :+ℕ ((n :*ℕ inc) :+ℕ slack))
    refl
    n low inc slack

strongerDistanceThresholdFitImpliesWeakerFit :
  (n low high budget : Nat) →
  DefectFloorStrengthening low high →
  BudgetFit n high budget →
  BudgetFit n low budget
strongerDistanceThresholdFitImpliesWeakerFit n low high budget strengthening strongFit =
  budgetFit
    (n * increment strengthening + slack strongFit)
    (trans
      (budgetDecomposition strongFit)
      rhs)
  where
  rhs :
    n * high + slack strongFit
      ≡ n * low + (n * increment strengthening + slack strongFit)
  rhs
    rewrite highIsLowPlusIncrement strengthening =
      populationCostDistributesOverFloorIncrease
        n low (increment strengthening) (slack strongFit)

------------------------------------------------------------------------
-- STRICT NESTING WITNESS
--
-- One pair of floor 1 fits budget 1 exactly.
-- One pair of floor 2 cannot fit the same budget with nonnegative slack.
-- Hence raising the defect floor can genuinely remove admissible populations.
------------------------------------------------------------------------

onePairFitsFloorOneBudgetOne : BudgetFit 1 1 1
onePairFitsFloorOneBudgetOne = budgetFit 0 refl

floorOneToFloorTwo : DefectFloorStrengthening 1 2
floorOneToFloorTwo = defectFloorStrengthening 1 refl

oneCannotEqualTwoPlusSlack :
  (s : Nat) → 1 ≡ 2 + s → ⊥
oneCannotEqualTwoPlusSlack s ()

onePairCannotFitFloorTwoBudgetOne : BudgetFit 1 2 1 → ⊥
onePairCannotFitFloorTwoBudgetOne fit =
  oneCannotEqualTwoPlusSlack (slack fit) (budgetDecomposition fit)

record StrictDistanceCeilingWitness : Set where
  constructor strictDistanceCeilingWitness
  field
    weakerThresholdFit : BudgetFit 1 1 1
    strongerThreshold : DefectFloorStrengthening 1 2
    strongerThresholdCannotFit : BudgetFit 1 2 1 → ⊥

strictDistanceCeilingWitness : StrictDistanceCeilingWitness
strictDistanceCeilingWitness =
  strictDistanceCeilingWitness
    onePairFitsFloorOneBudgetOne
    floorOneToFloorTwo
    onePairCannotFitFloorTwoBudgetOne

------------------------------------------------------------------------
-- INTERPRETATION FOR THE ZETA ROUTE
--
-- Exact observer order:
--
--   squared transverse defect  --->  fixed/off-line source signature
--
-- and not conversely.
--
-- Operationally, once a source-specific Hermitian producer supplies a
-- monotone defect floor f(delta) for |alpha| >= delta and an aggregate error
-- budget E(T), `BudgetFit` gives a nested family of distance-dependent pair
-- ceilings.  The existing inertia bound remains the uniform distance-blind
-- ceiling at the coarse level.  Their JOIN is therefore the natural object:
-- total pair control + increasingly strong far-off control.
------------------------------------------------------------------------

record DistanceStratifiedAnalyticAdapter : Set₁ where
  field
    Threshold : Set
    Pair : Set
    thresholdFloor : Threshold → Nat
    pairCountBeyondThreshold : Threshold → Nat
    arithmeticBudget : Threshold → Nat

    thresholdStrengthening :
      (low high : Threshold) → Set

    aggregateHermitianFit :
      (delta : Threshold) →
      BudgetFit
        (pairCountBeyondThreshold delta)
        (thresholdFloor delta)
        (arithmeticBudget delta)

record DistanceStratifiedObserverBoundary : Set where
  field
    visualizationUsedAsObserverOnly : Bool
    exactSignatureFactorizationThroughDefectProved : Bool
    reverseFactorizationAlreadyRefuted : Bool
    exactObserverStrictRefinementProved : Bool
    nestedBudgetCeilingTheoremProved : Bool
    strictNestingFiniteWitnessConstructed : Bool

    actualZetaMonotoneThresholdFloorInstantiatedHere : Bool
    sourceSpecificFarPairCeilingComputedHere : Bool
    rhStrengthNearLineClosureProvedHere : Bool

distanceStratifiedObserverBoundary : DistanceStratifiedObserverBoundary
distanceStratifiedObserverBoundary = record
  { visualizationUsedAsObserverOnly = true
  ; exactSignatureFactorizationThroughDefectProved = true
  ; reverseFactorizationAlreadyRefuted = true
  ; exactObserverStrictRefinementProved = true
  ; nestedBudgetCeilingTheoremProved = true
  ; strictNestingFiniteWitnessConstructed = true

  ; actualZetaMonotoneThresholdFloorInstantiatedHere = false
  ; sourceSpecificFarPairCeilingComputedHere = false
  ; rhStrengthNearLineClosureProvedHere = false
  }
