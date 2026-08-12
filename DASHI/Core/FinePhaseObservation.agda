module DASHI.Core.FinePhaseObservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)

import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Reasoning.RelationalBranchInterference as Interference

------------------------------------------------------------------------
-- Generic fine -> coarse observation.
--
-- The coarse phase is derived from the fine carrier.  It is not an independent
-- mutable truth value, and the interface deliberately supplies no inverse.
------------------------------------------------------------------------

record PhaseObservationSystem (Fine Coarse : Set) : Set₁ where
  constructor phaseObservationSystem
  field
    observePhase : Fine → Coarse

open PhaseObservationSystem public

record ObservedPhase
    {Fine Coarse : Set}
    (system : PhaseObservationSystem Fine Coarse)
    (fine : Fine) : Set where
  constructor observedPhase
  field
    coarse : Coarse
    coarseIsObservation : coarse ≡ observePhase system fine

open ObservedPhase public

data CoarsePhaseReconstructionPermission : Set where

coarsePhaseDoesNotReconstructFineEvidence :
  CoarsePhaseReconstructionPermission → ⊥
coarsePhaseDoesNotReconstructFineEvidence ()

------------------------------------------------------------------------
-- Canonical integer-sign instance using the repository's existing exact
-- signed-interaction classifier.
------------------------------------------------------------------------

integerPhaseDirection : ℤ → Selection.InteractionDirection
integerPhaseDirection value =
  Interference.interactionDirection
    (Interference.classifySignedInteraction value)

integerSignedPhaseSystem :
  PhaseObservationSystem ℤ Selection.InteractionDirection
integerSignedPhaseSystem = phaseObservationSystem integerPhaseDirection

observeIntegerPhase :
  (value : ℤ) →
  ObservedPhase integerSignedPhaseSystem value
observeIntegerPhase value =
  observedPhase (integerPhaseDirection value) refl
