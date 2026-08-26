module DASHI.Core.CoarseFineBranchAccessibilityExact where

------------------------------------------------------------------------
-- SOURCE / MATHEMATICAL NEIGHBOURHOOD
--
-- Theodore E. Harris, The Theory of Branching Processes,
-- Springer-Verlag, 1963.
--
-- This module extracts only the finite arithmetic skeleton used by DASHI:
-- for branching arity b and rational branch availability a/d, compare b*a
-- with d.  It does not construct a stochastic process, independence theorem,
-- Perron--Frobenius theory, or empirical probability model.
--
-- DASHI CONTRIBUTION
--
-- Keep three things separate:
--   * coarse observation,
--   * fine branch accessibility,
--   * regime classification from a declared finite availability ratio.
--
-- The observer theorem below reuses ObserverRefinementLatticeExact: if two
-- fine states share a coarse observation but expose different branch counts,
-- then (coarse, branch-count) is a strict refinement of coarse alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- Small executable arithmetic layer.
------------------------------------------------------------------------

data Order3 : Set where
  less equal greater : Order3

compareNat : Nat → Nat → Order3
compareNat zero zero = equal
compareNat zero (suc right) = less
compareNat (suc left) zero = greater
compareNat (suc left) (suc right) = compareNat left right

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc exponent) = base * pow base exponent

record RationalAvailability : Set where
  constructor availability
  field
    openNumerator : Nat
    totalDenominator : Nat

open RationalAvailability public

data BranchingRegime : Set where
  subcritical critical supercritical : BranchingRegime

reproductionNumerator : Nat → RationalAvailability → Nat
reproductionNumerator arity a = arity * openNumerator a

branchingRegime : Nat → RationalAvailability → BranchingRegime
branchingRegime arity a with compareNat (reproductionNumerator arity a) (totalDenominator a)
... | less = subcritical
... | equal = critical
... | greater = supercritical

------------------------------------------------------------------------
-- Exact critical reciprocals and the historical 5/18 specimen.
------------------------------------------------------------------------

binaryHalfCritical :
  branchingRegime 2 (availability 1 2) ≡ critical
binaryHalfCritical = refl

ternaryThirdCritical :
  branchingRegime 3 (availability 1 3) ≡ critical
ternaryThirdCritical = refl

quaternaryQuarterCritical :
  branchingRegime 4 (availability 1 4) ≡ critical
quaternaryQuarterCritical = refl

fiveEighteenthsTernarySubcritical :
  branchingRegime 3 (availability 5 18) ≡ subcritical
fiveEighteenthsTernarySubcritical = refl

threeTenthsTernarySubcritical :
  branchingRegime 3 (availability 3 10) ≡ subcritical
threeTenthsTernarySubcritical = refl

halfTernarySupercritical :
  branchingRegime 3 (availability 1 2) ≡ supercritical
halfTernarySupercritical = refl

------------------------------------------------------------------------
-- Product/intersection arithmetic.
--
-- Under an explicitly declared homogeneous independent toy model, d axes
-- each with b branches and availability a/q have expected accessible-cell
-- ratio
--
--     b^d * a^d / q^d.
--
-- These are arithmetic identities only.  No independence claim is inferred
-- for a real DASHI fibre or empirical system.
------------------------------------------------------------------------

jointExpectedNumerator :
  Nat → Nat → RationalAvailability → Nat
jointExpectedNumerator axisCount arity a =
  pow arity axisCount * pow (openNumerator a) axisCount

jointExpectedDenominator :
  Nat → RationalAvailability → Nat
jointExpectedDenominator axisCount a =
  pow (totalDenominator a) axisCount

threeAxisFiveEighteenthsNumerator :
  jointExpectedNumerator 3 3 (availability 5 18) ≡ 3375
threeAxisFiveEighteenthsNumerator = refl

threeAxisFiveEighteenthsDenominator :
  jointExpectedDenominator 3 (availability 5 18) ≡ 5832
threeAxisFiveEighteenthsDenominator = refl

threeAxisNinetyPercentNumerator :
  jointExpectedNumerator 3 3 (availability 9 10) ≡ 19683
threeAxisNinetyPercentNumerator = refl

threeAxisNinetyPercentDenominator :
  jointExpectedDenominator 3 (availability 9 10) ≡ 1000
threeAxisNinetyPercentDenominator = refl

------------------------------------------------------------------------
-- Coarse observer cannot in general recover branch accessibility.
------------------------------------------------------------------------

data ToyFineState : Set where
  narrow wide : ToyFineState

coarseToy : ToyFineState → Bool
coarseToy narrow = false
coarseToy wide = false

branchCountToy : ToyFineState → Nat
branchCountToy narrow = 1
branchCountToy wide = 3

branchCountDiffers :
  branchCountToy narrow ≡ branchCountToy wide → ⊥
branchCountDiffers ()

coarseBranchCountStrictRefinement :
  Observer.StrictRefinement
    coarseToy
    (Observer.pairObserver coarseToy branchCountToy)
coarseBranchCountStrictRefinement =
  Observer.strictPairRefinement
    coarseToy
    branchCountToy
    narrow
    wide
    refl
    branchCountDiffers

record CoarseFineBranchingBoundary : Set where
  constructor coarse-fine-branching-boundary
  field
    rationalRatioIsEmpiricalProbability : Bool
    independenceIsAutomatic : Bool
    branchCountDescendsThroughCoarseObserver : Bool
    spectralRadiusConstructedHere : Bool
    stochasticExtinctionTheoremConstructedHere : Bool

canonicalCoarseFineBranchingBoundary : CoarseFineBranchingBoundary
canonicalCoarseFineBranchingBoundary =
  coarse-fine-branching-boundary
    false
    false
    false
    false
    false
