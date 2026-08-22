module DASHI.Core.ResidualObserverDependencyRegression where

------------------------------------------------------------------------
-- FINITE REGRESSION FOR RESIDUAL OBSERVER DEPENDENCY
--
-- Two fine states have the same present coarse observation but different
-- action-indexed dependency codes.  Pairing the dependency observer with the
-- coarse observer is therefore a strict refinement, and no reconstruction map
-- from the coarse observation alone can recover the repair dependency code.
-- Separately, a concrete proof-bearing repair transition strictly decreases a
-- residual coupling score.  This is intentionally finite: it checks the
-- generic theorem seam without claiming affine spectral-independence or a
-- discrepancy bound.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.ResidualObserverDependencyExact as Residual

data LocalState : Set where
  entangled quiet healed : LocalState

data LocalAction : Set where
  repair inspect : LocalAction

data LocalIndex : Set where
  leftObserver rightObserver : LocalIndex

coarse : Observer.Observer LocalState Bool
coarse entangled = false
coarse quiet = false
coarse healed = true

------------------------------------------------------------------------
-- The relation says which residual observer may disturb which other observer
-- under a candidate action.  Only the entangled/repair state has the displayed
-- cross-observer influence.
------------------------------------------------------------------------

data LocalInfluence : LocalState → LocalAction → LocalIndex → LocalIndex → Set where
  entangledRepairCross :
    LocalInfluence entangled repair leftObserver rightObserver

dependencyCode : LocalState → LocalAction → Bool
dependencyCode entangled repair = true
dependencyCode entangled inspect = true
dependencyCode quiet repair = false
dependencyCode quiet inspect = false
dependencyCode healed repair = false
dependencyCode healed inspect = false

localResidualDependency :
  Residual.ResidualDependencyObserver
    LocalState LocalAction LocalIndex Bool
localResidualDependency = record
  { Influences = LocalInfluence
  ; dependencyCode = dependencyCode
  }

presentCollisionHidesRepairDependency :
  Residual.HiddenResidualDependency
    localResidualDependency coarse repair
presentCollisionHidesRepairDependency =
  Residual.hiddenResidualDependency
    entangled
    quiet
    refl
    (λ ())

repairDependencyStrictlyRefinesPresentObservation :
  Observer.StrictRefinement
    coarse
    (Residual.refinedObservationAt
      localResidualDependency coarse repair)
repairDependencyStrictlyRefinesPresentObservation =
  Residual.hiddenResidualDependencyGivesStrictRefinement
    presentCollisionHidesRepairDependency

repairDependencyDoesNotDescendThroughPresentObservation :
  Residual.DependencyCodeDescendsAt
    localResidualDependency coarse repair →
  ⊥
repairDependencyDoesNotDescendThroughPresentObservation =
  Residual.hiddenResidualDependencyBlocksDescent
    presentCollisionHidesRepairDependency

------------------------------------------------------------------------
-- Concrete admissible action system.
------------------------------------------------------------------------

data LocalPrecondition : LocalState → LocalAction → Set where
  repairEntangled : LocalPrecondition entangled repair
  inspectEntangled : LocalPrecondition entangled inspect
  inspectQuiet : LocalPrecondition quiet inspect
  inspectHealed : LocalPrecondition healed inspect

data LocalPostcondition :
    LocalState → LocalAction → LocalState → Set where
  repaired : LocalPostcondition entangled repair healed
  inspectedEntangled : LocalPostcondition entangled inspect entangled
  inspectedQuiet : LocalPostcondition quiet inspect quiet
  inspectedHealed : LocalPostcondition healed inspect healed

localActionSystem :
  Dependency.DependentActionSystem LocalState LocalAction
localActionSystem = record
  { Precondition = LocalPrecondition
  ; Postcondition = LocalPostcondition
  ; actionLabel = λ
      { repair → "repair"
      ; inspect → "inspect"
      }
  }

repairIsAdmissible :
  Dependency.AdmissibleAction localActionSystem entangled repair
repairIsAdmissible = record
  { precondition = repairEntangled
  ; after = healed
  ; postcondition = repaired
  ; dependencyReceipt =
      "repair is admitted only from the entangled fine state"
  }

inspectEntangledIsAdmissible :
  Dependency.AdmissibleAction localActionSystem entangled inspect
inspectEntangledIsAdmissible = record
  { precondition = inspectEntangled
  ; after = entangled
  ; postcondition = inspectedEntangled
  ; dependencyReceipt =
      "inspection preserves the entangled fine state"
  }

------------------------------------------------------------------------
-- Candidate ranking and realized decoupling are separate obligations.
------------------------------------------------------------------------

candidateCoupling : Residual.CouplingScore LocalState LocalAction
candidateCoupling entangled repair = 0
candidateCoupling entangled inspect = 1
candidateCoupling quiet repair = 0
candidateCoupling quiet inspect = 0
candidateCoupling healed repair = 0
candidateCoupling healed inspect = 0

repairIsLeastCoupledAdmissible :
  Residual.LeastCoupledAdmissibleChoice
    localActionSystem candidateCoupling entangled
repairIsLeastCoupledAdmissible = record
  { chosenAction = repair
  ; chosenAdmissible = repairIsAdmissible
  ; leastAmongAdmissible = λ
      { repair alternativeAdmissible → z≤n
      ; inspect alternativeAdmissible → z≤n
      }
  }

residualCoupling : Residual.ResidualStateScore LocalState
residualCoupling entangled = 1
residualCoupling quiet = 0
residualCoupling healed = 0

repairStrictlyDecouples :
  Residual.StrictlyDecouples residualCoupling repairIsAdmissible
repairStrictlyDecouples = s≤s z≤n

repairDecouples :
  Residual.Decouples residualCoupling repairIsAdmissible
repairDecouples =
  Residual.strictlyDecouplesImpliesDecouples repairStrictlyDecouples

------------------------------------------------------------------------
-- Exact regression boundary.
------------------------------------------------------------------------

record RegressionBoundary : Set where
  constructor regressionBoundary
  field
    samePresentObservation : coarse entangled ≡ coarse quiet
    differentRepairDependencyCannotCollapse :
      dependencyCode entangled repair ≡ dependencyCode quiet repair → ⊥
    repairDependencyCannotFactorThroughPresentObservation :
      Residual.DependencyCodeDescendsAt
        localResidualDependency coarse repair →
      ⊥
    realizedRepairStrictlyReducesCoupling :
      Residual.StrictlyDecouples residualCoupling repairIsAdmissible

canonicalRegressionBoundary : RegressionBoundary
canonicalRegressionBoundary =
  regressionBoundary
    refl
    (λ ())
    repairDependencyDoesNotDescendThroughPresentObservation
    repairStrictlyDecouples
