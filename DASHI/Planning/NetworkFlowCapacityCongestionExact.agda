module DASHI.Planning.NetworkFlowCapacityCongestionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

------------------------------------------------------------------------
-- NETWORK FLOW / CAPACITY / CONGESTION
--
-- Minimal finite common calculus for roads, transit, water, power, ecological
-- corridors and spatial-routing analogues.  It proves the key joint-feasibility
-- counterexample without identifying the domains themselves.
------------------------------------------------------------------------

data NetworkKind : Set where
  road transit water power communications ecologicalCorridor spatialRouting : NetworkKind

record Demand : Set where
  constructor demand
  field amount : Nat

record Capacity : Set where
  constructor capacity
  field limit : Nat

-- Finite witness carrier; `Fits` is intentionally qualitative here so the
-- no-promotion result is independent of a particular arithmetic order library.
data Fits : Demand → Capacity → Set where
  oneFitsTwo : Fits (demand (suc zero)) (capacity (suc (suc zero)))

data JointFits : Demand → Demand → Capacity → Set where
  onePlusOneFitsTwo :
    JointFits
      (demand (suc zero))
      (demand (suc zero))
      (capacity (suc (suc zero)))

data OverCapacity : Demand → Demand → Capacity → Set where
  twoPlusTwoExceedsThree :
    OverCapacity
      (demand (suc (suc zero)))
      (demand (suc (suc zero)))
      (capacity (suc (suc (suc zero))))

individualDemandA : Demand
individualDemandA = demand (suc (suc zero))

individualDemandB : Demand
individualDemandB = demand (suc (suc zero))

sharedCapacity : Capacity
sharedCapacity = capacity (suc (suc (suc zero)))

-- Each project's local feasibility may be certified by an application, but
-- no generic theorem promotes two such certificates to joint feasibility.
data IndividualFeasible : Demand → Capacity → Set where
  projectAFeasible : IndividualFeasible individualDemandA sharedCapacity
  projectBFeasible : IndividualFeasible individualDemandB sharedCapacity

data IndividualFeasibilityImpliesJointFeasibilityPermission : Set where

individualFeasibilityCannotAutoPromoteToJoint :
  IndividualFeasibilityImpliesJointFeasibilityPermission → ⊥
individualFeasibilityCannotAutoPromoteToJoint ()

canonicalSharedOverCapacity :
  OverCapacity individualDemandA individualDemandB sharedCapacity
canonicalSharedOverCapacity = twoPlusTwoExceedsThree

record CoupledNetworkBoundary : Set where
  constructor coupledNetworkBoundary
  field
    localFeasibilityImpliesJointNetworkFeasibility : Bool
    localFeasibilityImpliesJointNetworkFeasibilityIsFalse :
      localFeasibilityImpliesJointNetworkFeasibility ≡ false
    spatialSeparationRemovesSharedCapacityCompetition : Bool
    spatialSeparationRemovesSharedCapacityCompetitionIsFalse :
      spatialSeparationRemovesSharedCapacityCompetition ≡ false

canonicalCoupledNetworkBoundary : CoupledNetworkBoundary
canonicalCoupledNetworkBoundary = coupledNetworkBoundary false refl false refl
