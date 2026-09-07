module DASHI.Biology.SelfIndexedParetoHyperfabricTetrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as Self
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Core.NDimParetoHyperfabricExact as NDim

------------------------------------------------------------------------
-- SELF-INDEXED PARETO AXIS TOWER
--
-- If each site at level n is treated as one independently declared Pareto
-- coordinate, then the number of Pareto axes inherits the existing strong
-- self-indexing recurrence:
--
--   A_0 = 1
--   A_(n+1) = 9 ^ A_n.
--
-- This is genuine base-9 tetrational dimension growth.  It must be kept
-- distinct from the number of ternary objective profiles over those axes:
--
--   ProfileCount(n) = 3 ^ A_n.
------------------------------------------------------------------------

ParetoAxisAt : Nat → Set
ParetoAxisAt = Self.SelfIndexedCarrier

paretoAxisCount : Nat → Nat
paretoAxisCount = Self.selfIndexedSiteCount

paretoAxisCountZero : paretoAxisCount 0 ≡ 1
paretoAxisCountZero = refl

paretoAxisCountOne : paretoAxisCount 1 ≡ 9
paretoAxisCountOne = Self.selfIndexedLevelOneHasNineSites

paretoAxisCountRecurrence :
  (n : Nat) →
  paretoAxisCount (suc n) ≡ Hyper.powNat 9 (paretoAxisCount n)
paretoAxisCountRecurrence n = refl

paretoAxisCountIsNineTetration :
  (n : Nat) →
  paretoAxisCount n ≡ Hyper.nineTetration n
paretoAxisCountIsNineTetration = Self.selfIndexedCountEqualsNineTetration

TernaryObjectiveProfile : Nat → Set
TernaryObjectiveProfile n = ParetoAxisAt n → Trit.SSPTrit

ternaryObjectiveProfileCount : Nat → Nat
ternaryObjectiveProfileCount n = Hyper.powNat 3 (paretoAxisCount n)

levelZeroTernaryProfileCountIsThree :
  ternaryObjectiveProfileCount 0 ≡ 3
levelZeroTernaryProfileCountIsThree = refl

levelOneTernaryProfileCountIs19683 :
  ternaryObjectiveProfileCount 1 ≡ 19683
levelOneTernaryProfileCountIs19683 = refl

------------------------------------------------------------------------
-- Exact Base369 seam.
--
-- At self-indexing level one there are nine Pareto axes.  A ternary assignment
-- over those nine axes has 3^9 = 19683 profiles, exactly the same carrier count
-- as the existing three-voxel Base369 hyperfabric.  This is a cardinality/chart
-- seam only; it does not identify the constructions semantically.
------------------------------------------------------------------------

levelOneTernaryProfilesMatchBase369FabricCount :
  ternaryObjectiveProfileCount 1 ≡ Geometry.hyperfabricStateCount
levelOneTernaryProfilesMatchBase369FabricCount = refl

triadicTetrationLevelTwoIs27 :
  Tower.tetration 3 2 ≡ Geometry.hypervoxelStateCount
triadicTetrationLevelTwoIs27 = refl

------------------------------------------------------------------------
-- Important recursion distinction.
--
-- 27 occurs both as 3^^2 under the repo's finite tetration convention and as
-- one 3x3x3 ternary voxel.  19683 occurs as 3^9 and 27^3.  Neither numerical
-- coincidence turns product growth into tetrational self-indexing.
------------------------------------------------------------------------

record SelfIndexedParetoTetrationBoundary : Set where
  constructor selfIndexedParetoTetrationBoundary
  field
    paretoDimensionMayGrowTetrationally : Bool
    objectiveProfileCountEqualsParetoDimension : Bool
    levelOneNineAxisTernaryProfilesHave19683States : Bool
    base36919683CountImpliesSameSemanticConstruction : Bool
    twentySevenNumericalCoincidenceImpliesSameRecursiveRole : Bool
    productTwentySevenCubedIsDefinitionallyTetration : Bool
    paretoDominanceRemainsCoordinatewiseAtEveryLevel : Bool

canonicalSelfIndexedParetoTetrationBoundary :
  SelfIndexedParetoTetrationBoundary
canonicalSelfIndexedParetoTetrationBoundary =
  selfIndexedParetoTetrationBoundary true false true false false false true

existingSelfIndexingBoundary : Self.SelfIndexingHyperfabricBoundary
existingSelfIndexingBoundary = Self.canonicalSelfIndexingHyperfabricBoundary

existingNDimBoundary : NDim.NDimParetoHyperfabricBoundary
existingNDimBoundary = NDim.canonicalNDimParetoHyperfabricBoundary
