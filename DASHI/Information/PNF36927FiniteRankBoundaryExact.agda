module DASHI.Information.PNF36927FiniteRankBoundaryExact where

-- The 3/9/27 structural carriers of the existing 369/trialectic/pants
-- programme are not automatically sample sizes. Only an actual source
-- window with exactly that many observed rows triggers the corresponding
-- covariance rank-nullity bound.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _∸_; suc)
open import Data.Nat.Base using (_≤_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Information.PNFSampleMeanExact as Mean
import DASHI.Information.PNFFiniteRankNullityBridgeExact as Rank
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Branch

-- Exact existing carrier identities: three branch outputs, nine
-- observer positions and twenty-seven ternary hypervoxel states.
-- These equalities are *cardinality* information, not measurement receipts.
pantsThreeOutputs :
  Branch.outputCount
    Branch.composedOneToThree ≡ 3
pantsThreeOutputs = Pants.canonicalPantsHasThreeOutputs

observerNinePositions :
  Observer.observerPositionCount ≡ 9
observerNinePositions = Observer.observerPositionCountIsNine

hyperformTwentySevenStates :
  Fabric.hypervoxelStateCount ≡ 27
hyperformTwentySevenStates = Fabric.hypervoxelStateCountIs27

-- Conditional 3-actual-observation panel. The explicit mean certificate
-- is source-owned and must not be inferred from Pants.outputCount.
threeObservedRowsForcedNullity :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : Rank.FiniteFieldRankNullityOwner K) →
  {p : Nat} →
  (M : Mean.ActualFiniteMean K 3 p) →
  (scale : Scalar.Scalar (Ring.orderedScalar K)) →
  p ∸ 2 ≤ Rank.nullity O (Rank.covarianceLinearMap K M scale)
threeObservedRowsForcedNullity K O M scale =
  Rank.covarianceNullityAtLeastForcedLowerBound K O M scale

-- Conditional 9-actual-observation panel, independent of whether
-- the nine observer positions have ever been sampled as a data matrix.
nineObservedRowsForcedNullity :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : Rank.FiniteFieldRankNullityOwner K) →
  {p : Nat} →
  (M : Mean.ActualFiniteMean K 9 p) →
  (scale : Scalar.Scalar (Ring.orderedScalar K)) →
  p ∸ 8 ≤ Rank.nullity O (Rank.covarianceLinearMap K M scale)
nineObservedRowsForcedNullity K O M scale =
  Rank.covarianceNullityAtLeastForcedLowerBound K O M scale

-- Conditional 27-actual-observation panel. The 27-state 369 cube
-- is NOT assumed to be a 27-row source observation panel.
twentySevenObservedRowsForcedNullity :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : Rank.FiniteFieldRankNullityOwner K) →
  {p : Nat} →
  (M : Mean.ActualFiniteMean K 27 p) →
  (scale : Scalar.Scalar (Ring.orderedScalar K)) →
  p ∸ 26 ≤ Rank.nullity O (Rank.covarianceLinearMap K M scale)
twentySevenObservedRowsForcedNullity K O M scale =
  Rank.covarianceNullityAtLeastForcedLowerBound K O M scale
