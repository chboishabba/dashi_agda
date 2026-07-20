module DASHI.Physics.Closure.RepresentationKernelCompatibility where

-- Canonical foundations interface for changing representation while preserving
-- dynamics.  The central exact law is
--
--   project (fineStep x) ≡ coarseStep (project x)
--
-- on admissible states.  This module also derives trajectory, fixed-point, and
-- finite-reachability basin transport.  Approximate physics is never inferred
-- from low description length: the equivalence and defect budget are explicit
-- inputs.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Level; lsuc)
open import Data.Nat using (_≤_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Iteration.

iterate :
  ∀ {ℓ} {State : Set ℓ} →
  (State → State) → Nat → State → State
iterate step zero x = x
iterate step (suc n) x = step (iterate step n x)

------------------------------------------------------------------------
-- Exact representation/kernel compatibility.

record RepresentationKernelCompatibility {ℓ : Level} : Set (lsuc ℓ) where
  field
    FineState : Set ℓ
    CoarseState : Set ℓ
    Observable : Set ℓ

    fineStep : FineState → FineState
    coarseStep : CoarseState → CoarseState
    project : FineState → CoarseState

    fineAdmissible : FineState → Set ℓ
    coarseAdmissible : CoarseState → Set ℓ

    fineObserve : FineState → Observable
    coarseObserve : CoarseState → Observable

    fineAdmissibleStep :
      ∀ {x} → fineAdmissible x → fineAdmissible (fineStep x)

    coarseAdmissibleStep :
      ∀ {x} → coarseAdmissible x → coarseAdmissible (coarseStep x)

    projectPreservesAdmissibility :
      ∀ {x} → fineAdmissible x → coarseAdmissible (project x)

    projectPreservesObservable :
      ∀ x → coarseObserve (project x) ≡ fineObserve x

    kernelCommutesWithProjection :
      ∀ {x} →
      fineAdmissible x →
      project (fineStep x) ≡ coarseStep (project x)

open RepresentationKernelCompatibility public

iterateFineAdmissible :
  ∀ {ℓ}
    (law : RepresentationKernelCompatibility {ℓ})
    {x : FineState law} →
  fineAdmissible law x →
  ∀ n → fineAdmissible law (iterate (fineStep law) n x)
iterateFineAdmissible law admissible zero = admissible
iterateFineAdmissible law admissible (suc n) =
  fineAdmissibleStep law (iterateFineAdmissible law admissible n)

iterateCoarseAdmissible :
  ∀ {ℓ}
    (law : RepresentationKernelCompatibility {ℓ})
    {x : CoarseState law} →
  coarseAdmissible law x →
  ∀ n → coarseAdmissible law (iterate (coarseStep law) n x)
iterateCoarseAdmissible law admissible zero = admissible
iterateCoarseAdmissible law admissible (suc n) =
  coarseAdmissibleStep law (iterateCoarseAdmissible law admissible n)

trajectoryCommutes :
  ∀ {ℓ}
    (law : RepresentationKernelCompatibility {ℓ})
    {x : FineState law} →
  fineAdmissible law x →
  ∀ n →
  project law (iterate (fineStep law) n x)
  ≡
  iterate (coarseStep law) n (project law x)
trajectoryCommutes law admissible zero = refl
trajectoryCommutes law admissible (suc n) =
  trans
    (kernelCommutesWithProjection law
      (iterateFineAdmissible law admissible n))
    (cong (coarseStep law) (trajectoryCommutes law admissible n))

trajectoryObservablePreserved :
  ∀ {ℓ}
    (law : RepresentationKernelCompatibility {ℓ})
    {x : FineState law} →
  fineAdmissible law x →
  ∀ n →
  coarseObserve law
    (iterate (coarseStep law) n (project law x))
  ≡
  fineObserve law
    (iterate (fineStep law) n x)
trajectoryObservablePreserved law {x} admissible n =
  trans
    (cong (coarseObserve law)
      (sym (trajectoryCommutes law admissible n)))
    (projectPreservesObservable law
      (iterate (fineStep law) n x))

------------------------------------------------------------------------
-- Dynamical shapes preserved by exact compatibility.

FixedPoint :
  ∀ {ℓ} {State : Set ℓ} →
  (State → State) → State → Set ℓ
FixedPoint step x = step x ≡ x

projectedFixedPoint :
  ∀ {ℓ}
    (law : RepresentationKernelCompatibility {ℓ})
    {x : FineState law} →
  fineAdmissible law x →
  FixedPoint (fineStep law) x →
  FixedPoint (coarseStep law) (project law x)
projectedFixedPoint law admissible fixed =
  trans
    (sym (kernelCommutesWithProjection law admissible))
    (cong (project law) fixed)

EventuallyReaches :
  ∀ {ℓ} {State : Set ℓ} →
  (State → State) → State → State → Set ℓ
EventuallyReaches step x target =
  Σ Nat (λ n → iterate step n x ≡ target)

projectedEventuallyReaches :
  ∀ {ℓ}
    (law : RepresentationKernelCompatibility {ℓ})
    {x target : FineState law} →
  fineAdmissible law x →
  EventuallyReaches (fineStep law) x target →
  EventuallyReaches
    (coarseStep law)
    (project law x)
    (project law target)
projectedEventuallyReaches law admissible (n , reaches) =
  n ,
  trans
    (sym (trajectoryCommutes law admissible n))
    (cong (project law) reaches)

------------------------------------------------------------------------
-- Explicit same-physics data.  Equality of numerical values alone is not the
-- definition: admissibility, selected observables, invariants, and causal
-- support are named separately.

record SamePhysicsStructure {ℓ : Level}
  (State Observable Invariant Support : Set ℓ) : Set (lsuc ℓ) where
  field
    admissible : State → Set ℓ
    observe : State → Observable
    invariant : State → Invariant
    causalSupport : State → Support

    sameObservable : Observable → Observable → Set ℓ
    sameInvariant : Invariant → Invariant → Set ℓ
    sameSupport : Support → Support → Set ℓ

record SamePhysicsWitness {ℓ : Level}
  {State Observable Invariant Support : Set ℓ}
  (structure : SamePhysicsStructure State Observable Invariant Support)
  (x y : State) : Set ℓ where
  open SamePhysicsStructure structure
  field
    leftAdmissible : admissible x
    rightAdmissible : admissible y
    observableAgrees : sameObservable (observe x) (observe y)
    invariantAgrees : sameInvariant (invariant x) (invariant y)
    causalSupportAgrees : sameSupport (causalSupport x) (causalSupport y)

------------------------------------------------------------------------
-- Approximate/quotient compatibility with an explicit n-step defect budget.

record ApproxRepresentationKernelCompatibility {ℓ : Level} : Set (lsuc ℓ) where
  field
    FineState : Set ℓ
    CoarseState : Set ℓ
    Observable : Set ℓ

    fineStep : FineState → FineState
    coarseStep : CoarseState → CoarseState
    project : FineState → CoarseState

    fineAdmissible : FineState → Set ℓ
    coarseAdmissible : CoarseState → Set ℓ

    sameCoarsePhysics : CoarseState → CoarseState → Set ℓ
    sameObservable : Observable → Observable → Set ℓ

    fineObserve : FineState → Observable
    coarseObserve : CoarseState → Observable

    projectPreservesAdmissibility :
      ∀ {x} → fineAdmissible x → coarseAdmissible (project x)

    observableTransport :
      ∀ x → sameObservable (coarseObserve (project x)) (fineObserve x)

    kernelCommutesUpToPhysics :
      ∀ {x} →
      fineAdmissible x →
      sameCoarsePhysics
        (project (fineStep x))
        (coarseStep (project x))

    trajectoryDefect : Nat → FineState → Nat
    defectBudget : Nat → Nat

    trajectoryDefectBound :
      ∀ {x} →
      fineAdmissible x →
      ∀ n → trajectoryDefect n x ≤ defectBudget n

------------------------------------------------------------------------
-- MDL chooses inside an already established lawful equivalence class.

record MDLRepresentativeSelection {ℓ : Level}
  (law : ApproxRepresentationKernelCompatibility {ℓ}) : Set (lsuc ℓ) where
  open ApproxRepresentationKernelCompatibility law
  field
    cost : CoarseState → Nat
    canonicalRepresentative : CoarseState → CoarseState

    representativePreservesPhysics :
      ∀ x → sameCoarsePhysics (canonicalRepresentative x) x

    representativeDoesNotIncreaseCost :
      ∀ x → cost (canonicalRepresentative x) ≤ cost x

    canonicalRepresentativeIdempotent :
      ∀ x →
      canonicalRepresentative (canonicalRepresentative x)
      ≡ canonicalRepresentative x
