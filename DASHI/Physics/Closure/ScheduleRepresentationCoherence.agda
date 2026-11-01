module DASHI.Physics.Closure.ScheduleRepresentationCoherence where

-- Two-dimensional coherence surface.
--
-- Representation coherence varies the carrier through project.
-- Schedule coherence varies the permissible ordering/selection of local update
-- operations.  This module does not assert Wolfram-style causal invariance; it
-- states the exact obligations needed to combine that axis with DASHI carrier
-- compatibility.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Level; lsuc)

import DASHI.Physics.Closure.RepresentationKernelCompatibility as RKC

record ScheduleRepresentationCoherence {ℓ : Level} : Set (lsuc ℓ) where
  field
    FineState : Set ℓ
    CoarseState : Set ℓ
    Schedule : Set ℓ

    admissibleSchedule : Schedule → Set ℓ
    fineAdmissible : FineState → Set ℓ
    coarseAdmissible : CoarseState → Set ℓ

    fineScheduledStep : Schedule → FineState → FineState
    coarseStep : CoarseState → CoarseState
    project : FineState → CoarseState

    sameCoarsePhysics : CoarseState → CoarseState → Set ℓ

    fineAdmissibleStep :
      ∀ {σ x} →
      admissibleSchedule σ →
      fineAdmissible x →
      fineAdmissible (fineScheduledStep σ x)

    projectPreservesAdmissibility :
      ∀ {x} → fineAdmissible x → coarseAdmissible (project x)

    everyAdmissibleScheduleCommutesWithProjection :
      ∀ {σ x} →
      admissibleSchedule σ →
      fineAdmissible x →
      sameCoarsePhysics
        (project (fineScheduledStep σ x))
        (coarseStep (project x))

    admissibleSchedulesAgreeAfterProjection :
      ∀ {σ τ x} →
      admissibleSchedule σ →
      admissibleSchedule τ →
      fineAdmissible x →
      sameCoarsePhysics
        (project (fineScheduledStep σ x))
        (project (fineScheduledStep τ x))

------------------------------------------------------------------------
-- A schedule trace and its projected n-step obligation.

ScheduleTrace :
  ∀ {ℓ} → Set ℓ → Set ℓ
ScheduleTrace Schedule = Nat → Schedule

scheduledIterate :
  ∀ {ℓ} {State Schedule : Set ℓ} →
  (Schedule → State → State) →
  ScheduleTrace Schedule →
  Nat → State → State
scheduledIterate step trace zero x = x
scheduledIterate step trace (suc n) x =
  step (trace n) (scheduledIterate step trace n x)

record ScheduledTrajectoryCoherence {ℓ : Level}
  (law : ScheduleRepresentationCoherence {ℓ}) : Set (lsuc ℓ) where
  open ScheduleRepresentationCoherence law
  field
    trace : ScheduleTrace Schedule
    traceAdmissible : ∀ n → admissibleSchedule (trace n)

    projectedTrajectoryCoherent :
      ∀ {x} →
      fineAdmissible x →
      ∀ n →
      sameCoarsePhysics
        (project (scheduledIterate fineScheduledStep trace n x))
        (RKC.iterate coarseStep n (project x))
