module DASHI.Computation.BMSSPWorkPivotTemporalTransportExact where

-- Temporal transport laws for the same-carrier BMSSP layer.
-- Completed work and pivot coverage are intentionally different temporal
-- objects: completed work may be persistent, while pivot coverage may be
-- discharged into work or re-established by a (possibly different) pivot.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Computation.SSSPGeneralPullPrefixQuotientExact as Pull
import DASHI.Computation.BMSSPPullPivotTemporalSameCarrierExact as Same
import DASHI.Computation.PathfindingTemporalFibreEvolutionExact as Temporal

------------------------------------------------------------------------
-- 1. Completed-work persistence on the literal recursive transition.
------------------------------------------------------------------------

record CompletedWorkPersistence
  (B : Same.BMSSPTemporalSameCarrier) : Set₁ where
  constructor completedWorkPersistence
  field
    persists :
      (t : Nat) (x : Pull.FullState (Same.pull B)) →
      Same.InCompletedWork (Same.pivotLayer B t) x →
      Same.InCompletedWork
        (Same.pivotLayer B (suc t))
        (Same.advance (Same.transition B) t x)

open CompletedWorkPersistence public

------------------------------------------------------------------------
-- 2. Target coverage is theorem-bearing at every time slice.
------------------------------------------------------------------------

targetCoverage :
  (B : Same.BMSSPTemporalSameCarrier) →
  (t : Nat) →
  (x : Pull.FullState (Same.pull B)) →
  Same.InCompletedWork
    (Same.pivotLayer B (suc t))
    (Same.advance (Same.transition B) t x)
  ⊎
  Same.VisitsCompletePivot
    (Same.pivotLayer B (suc t))
    (Same.advance (Same.transition B) t x)
targetCoverage B t x =
  Same.coverage (Same.pivotLayer B (suc t))
    (Same.advance (Same.transition B) t x)

completedWorkStaysCovered :
  (B : Same.BMSSPTemporalSameCarrier) →
  CompletedWorkPersistence B →
  (t : Nat) (x : Pull.FullState (Same.pull B)) →
  Same.InCompletedWork (Same.pivotLayer B t) x →
  Same.InCompletedWork
    (Same.pivotLayer B (suc t))
    (Same.advance (Same.transition B) t x)
  ⊎
  Same.VisitsCompletePivot
    (Same.pivotLayer B (suc t))
    (Same.advance (Same.transition B) t x)
completedWorkStaysCovered B W t x done = inj₁ (persists W t x done)

------------------------------------------------------------------------
-- 3. Pivot evolution is a target-state dichotomy, not identical persistence.
------------------------------------------------------------------------

data PivotAfterStep
  (B : Same.BMSSPTemporalSameCarrier)
  (t : Nat)
  (x : Pull.FullState (Same.pull B)) : Set where
  pivotDischargedIntoCompletedWork :
    Same.InCompletedWork
      (Same.pivotLayer B (suc t))
      (Same.advance (Same.transition B) t x) →
    PivotAfterStep B t x

  pivotCoverageReestablished :
    Same.VisitsCompletePivot
      (Same.pivotLayer B (suc t))
      (Same.advance (Same.transition B) t x) →
    PivotAfterStep B t x

classifyPivotAfterStep :
  (B : Same.BMSSPTemporalSameCarrier) →
  (t : Nat) →
  (x : Pull.FullState (Same.pull B)) →
  Same.VisitsCompletePivot (Same.pivotLayer B t) x →
  PivotAfterStep B t x
classifyPivotAfterStep B t x oldPivot with targetCoverage B t x
... | inj₁ done = pivotDischargedIntoCompletedWork done
... | inj₂ pivot = pivotCoverageReestablished pivot

------------------------------------------------------------------------
-- 4. Residual evolution is separately typed.
------------------------------------------------------------------------

record BMSSPResidualTransportWitness
  (B : Same.BMSSPTemporalSameCarrier) : Set₁ where
  constructor bmsspResidualTransportWitness
  field
    evolutionKind :
      (t : Nat) → Temporal.ResidualEvolutionKind
    relatesTail :
      (t : Nat) →
      Pull.TailCode (Same.pull B) →
      Pull.TailCode (Same.pull B) → Set
    currentTailRelated :
      (t : Nat) →
      relatesTail t
        (Same.currentTail B t)
        (Same.currentTail B (suc t))

open BMSSPResidualTransportWitness public

------------------------------------------------------------------------
-- 5. Boundary: persistence is not conflated with pivot validity.
------------------------------------------------------------------------

record BMSSPWorkPivotTemporalBoundary : Set where
  constructor bmsspWorkPivotTemporalBoundary
  field
    completedWorkMayHavePersistenceLaw : Bool
    completedWorkMayHavePersistenceLawIsTrue :
      completedWorkMayHavePersistenceLaw ≡ true

    pivotCoverageMustPersistIdentically : Bool
    pivotCoverageMustPersistIdenticallyIsFalse :
      pivotCoverageMustPersistIdentically ≡ false

    pivotTargetStatusIsProofClassified : Bool
    pivotTargetStatusIsProofClassifiedIsTrue :
      pivotTargetStatusIsProofClassified ≡ true

    targetCoverageMustBeReestablished : Bool
    targetCoverageMustBeReestablishedIsTrue :
      targetCoverageMustBeReestablished ≡ true

    residualTailMayRefineOrReopen : Bool
    residualTailMayRefineOrReopenIsTrue :
      residualTailMayRefineOrReopen ≡ true

canonicalBMSSPWorkPivotTemporalBoundary : BMSSPWorkPivotTemporalBoundary
canonicalBMSSPWorkPivotTemporalBoundary =
  bmsspWorkPivotTemporalBoundary true refl false refl true refl true refl true refl
