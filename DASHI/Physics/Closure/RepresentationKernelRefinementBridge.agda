module DASHI.Physics.Closure.RepresentationKernelRefinementBridge where

-- Consolidates the new canonical compatibility interface with the pre-existing
-- DASHI.Physics.Refinement commuting-square spine.

open import Agda.Primitive using (Level; lsuc)

import DASHI.Physics.PhysicalTheory as PT
import DASHI.Physics.Refinement as Refinement
import DASHI.Physics.Closure.RepresentationKernelCompatibility as RKC

record ObservableRefinementBridge {ℓ : Level}
  (coarse fine : PT.PhysicalTheory ℓ)
  (refinement : Refinement.RefinementStep coarse fine) : Set (lsuc ℓ) where
  field
    Observable : Set ℓ
    fineObserve : PT.State fine → Observable
    coarseObserve : PT.State coarse → Observable

    observableProjects :
      ∀ x →
      coarseObserve (Refinement.RefinementStep.project refinement x)
      ≡
      fineObserve x

open ObservableRefinementBridge public

refinementToRepresentationKernelCompatibility :
  ∀ {ℓ}
    {coarse fine : PT.PhysicalTheory ℓ}
    {refinement : Refinement.RefinementStep coarse fine} →
  ObservableRefinementBridge coarse fine refinement →
  RKC.RepresentationKernelCompatibility
refinementToRepresentationKernelCompatibility
  {coarse = coarse}
  {fine = fine}
  {refinement = refinement}
  observableBridge =
  record
    { FineState = PT.State fine
    ; CoarseState = PT.State coarse
    ; Observable = Observable observableBridge
    ; fineStep = PT.step fine
    ; coarseStep = PT.step coarse
    ; project = Refinement.RefinementStep.project refinement
    ; fineAdmissible = PT.Inv fine
    ; coarseAdmissible = PT.Inv coarse
    ; fineObserve = fineObserve observableBridge
    ; coarseObserve = coarseObserve observableBridge
    ; fineAdmissibleStep = PT.inv-step fine
    ; coarseAdmissibleStep = PT.inv-step coarse
    ; projectPreservesAdmissibility =
        Refinement.RefinementStep.project-inv refinement
    ; projectPreservesObservable = observableProjects observableBridge
    ; kernelCommutesWithProjection =
        Refinement.RefinementStep.commute-project refinement
    }

record ApproxObservableRefinementBridge {ℓ : Level}
  (coarse fine : PT.PhysicalTheory ℓ)
  (refinement : Refinement.ApproxRefinementStep coarse fine) : Set (lsuc ℓ) where
  field
    Observable : Set ℓ
    fineObserve : PT.State fine → Observable
    coarseObserve : PT.State coarse → Observable
    sameObservable : Observable → Observable → Set ℓ

    observableProjects :
      ∀ x →
      sameObservable
        (coarseObserve
          (Refinement.ApproxRefinementStep.project refinement x))
        (fineObserve x)
