module DASHI.Physics.Closure.RepresentationAttractorTransport where

-- Metric/convergence-facing extension of exact representation compatibility.
-- The core module already proves transport of fixed points and finite-time
-- reachability.  Genuine attractor transport additionally needs a chosen
-- convergence notion and a proof that projection preserves it; those data are
-- explicit here rather than hidden behind the word "shape".

open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Level; lsuc)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_)

import DASHI.Physics.Closure.RepresentationKernelCompatibility as RKC

Orbit :
  ∀ {ℓ} {State : Set ℓ} →
  (State → State) → State → Nat → State
Orbit step x n = RKC.iterate step n x

record ConvergenceStructure {ℓ : Level} (State : Set ℓ) : Set (lsuc ℓ) where
  field
    distance : State → State → Nat
    convergesTo : (Nat → State) → State → Set ℓ

record AttractorBasin {ℓ : Level}
  {State : Set ℓ}
  (step : State → State)
  (admissible : State → Set ℓ)
  (convergence : ConvergenceStructure State)
  (target : State) : Set (lsuc ℓ) where
  open ConvergenceStructure convergence
  field
    member : State → Set ℓ
    memberSound :
      ∀ {x} →
      member x →
      admissible x × convergesTo (Orbit step x) target

record RepresentationAttractorCompatibility {ℓ : Level}
  (law : RKC.RepresentationKernelCompatibility {ℓ}) : Set (lsuc ℓ) where
  open RKC.RepresentationKernelCompatibility law
  field
    fineConvergence : ConvergenceStructure FineState
    coarseConvergence : ConvergenceStructure CoarseState

    projectionNonexpansive :
      ∀ x y →
      ConvergenceStructure.distance coarseConvergence (project x) (project y)
      ≤
      ConvergenceStructure.distance fineConvergence x y

    projectionPreservesConvergence :
      ∀ {x target} →
      fineAdmissible x →
      ConvergenceStructure.convergesTo fineConvergence
        (Orbit fineStep x)
        target →
      ConvergenceStructure.convergesTo coarseConvergence
        (Orbit coarseStep (project x))
        (project target)

projectedAttractorBasinMember :
  ∀ {ℓ}
    {law : RKC.RepresentationKernelCompatibility {ℓ}}
    (compatibility : RepresentationAttractorCompatibility law)
    {x target} →
  RKC.fineAdmissible law x →
  ConvergenceStructure.convergesTo
    (RepresentationAttractorCompatibility.fineConvergence compatibility)
    (Orbit (RKC.fineStep law) x)
    target →
  ConvergenceStructure.convergesTo
    (RepresentationAttractorCompatibility.coarseConvergence compatibility)
    (Orbit (RKC.coarseStep law) (RKC.project law x))
    (RKC.project law target)
projectedAttractorBasinMember compatibility =
  RepresentationAttractorCompatibility.projectionPreservesConvergence
    compatibility
