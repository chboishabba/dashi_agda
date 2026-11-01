module DASHI.Moonshine.MonsterThreeLocalE8LeechBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hiroki Shimakura,
-- "An E8-approach to the moonshine vertex operator algebra",
-- Journal of the London Mathematical Society 83 (2011), 493--516.
-- DOI: 10.1112/jlms/jdq078.
--
-- Hsian-Yang Chen, Ching Hung Lam and Hiroki Shimakura,
-- "Z_3-orbifold construction of the Moonshine vertex operator algebra and
-- some maximal 3-local subgroups of the Monster",
-- Mathematische Zeitschrift 288 (2018), 75--100.
-- DOI: 10.1007/s00209-017-1878-z.
--
-- J. H. Conway and N. J. A. Sloane,
-- "The Coxeter--Todd lattice, the Mitchell group, and related sphere
-- packings",
-- Mathematical Proceedings of the Cambridge Philosophical Society 93
-- (1983), 421--440.
-- DOI: 10.1017/S0305004100060746.
--
-- IN-REPOSITORY AUTHORITY
--
-- DASHI.Biology.ExceptionalLatticeGrokkingProtocolExact already records the
-- E8 rank 8, its 240 roots, the Leech rank 24, and its 196560 minimal vectors.
--
-- DASHI CONTRIBUTION
--
-- Keep four objects with the same visible numeral separate:
--
--   * the rank-eight E8 lattice;
--   * the eight-dimensional F3 quadratic space underlying
--       3^8.Omega^-(8,3).2;
--   * the rank-24 Leech lattice used in the orbifold construction;
--   * the six-dimensional Lagrangian coordinate of the finite Heisenberg
--       representation for 3^(1+12).
--
-- The two Monster 3-local charts are nevertheless arithmetically compatible:
--
--   10 * 3^8 = 90 * 3^6 = 65610.
--
-- This is an exact common refinement of dimensions.  It is not an equality
-- of the two maximal 3-local subgroups or of their actions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Biology.ExceptionalLatticeGrokkingProtocolExact as Existing

eightRankE8 : Nat
eightRankE8 = Existing.ambientDimension Existing.E8Benchmark

eightRankE8IsEight : eightRankE8 ≡ 8
eightRankE8IsEight = refl

e8RootCount : Nat
e8RootCount = Existing.shortestVectorCount Existing.E8Benchmark

e8RootCountIs240 : e8RootCount ≡ 240
e8RootCountIs240 = refl

leechRank : Nat
leechRank = Existing.ambientDimension Existing.LeechBenchmark

leechRankIs24 : leechRank ≡ 24
leechRankIs24 = refl

leechMinimalVectorCount : Nat
leechMinimalVectorCount = Existing.shortestVectorCount Existing.LeechBenchmark

leechMinimalVectorCountIs196560 : leechMinimalVectorCount ≡ 196560
leechMinimalVectorCountIs196560 = refl

threePowerSix : Nat
threePowerSix = 729

threePowerEight : Nat
threePowerEight = 6561

threePowerEightIsNineTimesThreePowerSix :
  threePowerEight ≡ 9 * threePowerSix
threePowerEightIsNineTimesThreePowerSix = refl

tenTimesThreePowerEight : Nat
tenTimesThreePowerEight = 10 * threePowerEight

ninetyTimesThreePowerSix : Nat
ninetyTimesThreePowerSix = 90 * threePowerSix

twoThreeLocalChartsShare65610 :
  tenTimesThreePowerEight ≡ ninetyTimesThreePowerSix
twoThreeLocalChartsShare65610 = refl

tenTimesThreePowerEightIs65610 : tenTimesThreePowerEight ≡ 65610
tenTimesThreePowerEightIs65610 = refl

ninetyTimesThreePowerSixIs65610 : ninetyTimesThreePowerSix ≡ 65610
ninetyTimesThreePowerSixIs65610 = refl

------------------------------------------------------------------------
-- A sourced E8-to-Leech counting chart.
--
-- One standard octonionic description counts the 196560 Leech minimal
-- vectors as three E8-root families with multiplicities 1, 16 and 16^2.
-- This is recorded as arithmetic only; no particular coordinate realization
-- is imported by this file.
------------------------------------------------------------------------

eightToLeechMultiplier : Nat
eightToLeechMultiplier = 3 * (1 + 16 + 16 * 16)

eightToLeechMultiplierIs819 : eightToLeechMultiplier ≡ 819
eightToLeechMultiplierIs819 = refl

e8RootsGenerateLeechMinimalCountArithmetic :
  e8RootCount * eightToLeechMultiplier ≡ leechMinimalVectorCount
e8RootsGenerateLeechMinimalCountArithmetic = refl

data EightDimensionalRole : Set where
  e8EuclideanLatticeRank : EightDimensionalRole
  finiteQuadraticSpaceOverF3 : EightDimensionalRole
  simpleCurrentGradingRank : EightDimensionalRole

data ThreeLocalRole : Set where
  elementaryAbelianThreePowerEight : ThreeLocalRole
  extraspecialThreePowerOnePlusTwelve : ThreeLocalRole
  heisenbergLagrangianThreePowerSix : ThreeLocalRole

record ThreeLocalObjectBoundary : Set where
  constructor threeLocalObjectBoundary
  field
    e8LatticeEqualsF3EightQuadraticSpace : Bool
    e8LatticeEqualsF3EightQuadraticSpaceIsFalse :
      e8LatticeEqualsF3EightQuadraticSpace ≡ false
    threePowerEightSubgroupEqualsExtraspecialKernel : Bool
    threePowerEightSubgroupEqualsExtraspecialKernelIsFalse :
      threePowerEightSubgroupEqualsExtraspecialKernel ≡ false
    bothOccurInSourcedMoonshineVOAConstructions : Bool
    bothOccurInSourcedMoonshineVOAConstructionsIsTrue :
      bothOccurInSourcedMoonshineVOAConstructions ≡ true
    dimensionRefactorizationIsExact : Bool
    dimensionRefactorizationIsExactIsTrue :
      dimensionRefactorizationIsExact ≡ true
    dimensionRefactorizationProvesEquivariantEquivalence : Bool
    dimensionRefactorizationProvesEquivariantEquivalenceIsFalse :
      dimensionRefactorizationProvesEquivariantEquivalence ≡ false

canonicalThreeLocalObjectBoundary : ThreeLocalObjectBoundary
canonicalThreeLocalObjectBoundary =
  threeLocalObjectBoundary
    false refl
    false refl
    true refl
    true refl
    false refl
