module DASHI.Biology.BH4AllocatorFutureObservationCountermodelExact where

-- Highest-value BH4/future-observer negative control.
-- One shared stoichiometrically balanced resource total is NOT a
-- future-sufficient representation of branch-specific enzyme allocation.
-- This is a finite, exact counterexample, not an asserted Kitzerow
-- clinical mechanism, patient result, or fitted cellular flux.

open import DASHI.Core.Prelude
import DASHI.Biology.BH4SystemStateExact as BH4
import DASHI.Biology.BH4JointFluxFeasibilityExact as Feasibility
import DASHI.Biology.BH4OpenMetabolicNetworkAdapterExact as Metabolism

record BalancedBranchAllocation : Set where
  constructor balanced-branch-allocation
  field
    commonSupply : Nat
    synthesisUse : Nat
    recyclingUse : Nat
    hydroxylaseBranch : Nat
    nitricOxideSynthaseBranch : Nat
    otherBranch : Nat
    oxidativeLoss : Nat
    storedIncrement : Nat
    commonSupplyIdentifiesSource :
      commonSupply ≡ synthesisUse + recyclingUse
    sourceBalance :
      synthesisUse + recyclingUse
        ≡ hydroxylaseBranch + nitricOxideSynthaseBranch
          + otherBranch + oxidativeLoss + storedIncrement
    -- No omitted exchange is implicitly counted as zero: this is a
    -- closed selected fixture with separately explicit coordinates.

open BalancedBranchAllocation public

branchResponse : BalancedBranchAllocation → Bool
branchResponse (balanced-branch-allocation _ _ _ h _ _ _ _ _ _) with h
... | zero = false
... | suc _ = true

-- Both candidates have the same paid influx of one (same coarse supply),
-- satisfy their finite balance equations, yet choose different demands.
hydroxylasePriority nitricOxidePriority : BalancedBranchAllocation
hydroxylasePriority =
  balanced-branch-allocation 1 1 0 1 0 0 0 0 refl refl
nitricOxidePriority =
  balanced-branch-allocation 1 1 0 0 1 0 0 0 refl refl

sameCoarseSupply :
  commonSupply hydroxylasePriority
    ≡ commonSupply nitricOxidePriority
sameCoarseSupply = refl

branchSensitiveResultA :
  branchResponse hydroxylasePriority ≡ true
branchSensitiveResultA = refl

branchSensitiveResultB :
  branchResponse nitricOxidePriority ≡ false
branchSensitiveResultB = refl

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

supplyOnlyNotSufficientForBranchFuture :
  (allPredictions : Nat → Bool)
  (factor : (candidate : BalancedBranchAllocation) →
    branchResponse candidate ≡ allPredictions (commonSupply candidate)) →
  ⊥
supplyOnlyNotSufficientForBranchFuture allPredictions factor =
  falseNotTrue
    (trans
      (trans
        (sym branchSensitiveResultB)
        (factor nitricOxidePriority))
      (trans
        (cong allPredictions (sym sameCoarseSupply))
        (trans
          (sym (factor hydroxylasePriority))
          branchSensitiveResultA)))

-- Canonical unpromoted original physical data owners are imported, but
-- they cannot manufacture this allocation as measured physiological flux.
physicalBH4StateType : Set
physicalBH4StateType = BH4.BH4SystemState

sourceBalanceWitnessType : BH4.BH4SystemState → Set
sourceBalanceWitnessType = BH4.FluxBalanceWitness

actualFluxCandidateType : Set
actualFluxCandidateType = Feasibility.BH4JointFluxFeasibility

openNetworkAdapterType : Set
openNetworkAdapterType = Metabolism.BH4OpenMetabolicNetworkAdapter
