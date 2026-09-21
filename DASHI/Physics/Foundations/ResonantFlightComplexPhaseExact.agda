module DASHI.Physics.Foundations.ResonantFlightComplexPhaseExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Complex-amplitude style coordinates without committing this structural
-- layer to a concrete complex-number implementation.
------------------------------------------------------------------------

record ComplexAmplitudePhase : Set₁ where
  constructor complex-amplitude-phase
  field
    Amplitude Phase : Set
    amplitude : Amplitude
    phase : Phase

open ComplexAmplitudePhase public

record PhaseGroup : Set₁ where
  constructor phase-group
  field
    Phase : Set
    _⊕_ _⊖_ : Phase → Phase → Phase
    zero : Phase
    right-zero : (φ : Phase) → φ ⊖ zero ≡ φ

open PhaseGroup public

relativePhase :
  (P : PhaseGroup) →
  PhaseGroup.Phase P →
  PhaseGroup.Phase P →
  PhaseGroup.Phase P
relativePhase P φ ψ = PhaseGroup._⊖_ P φ ψ

relativeToZeroIsSelf :
  (P : PhaseGroup) →
  (φ : PhaseGroup.Phase P) →
  relativePhase P φ (PhaseGroup.zero P) ≡ φ
relativeToZeroIsSelf P = PhaseGroup.right-zero P

record ModalPhasorBank : Set₁ where
  constructor modal-phasor-bank
  field
    Mode : Set
    Coordinate : Mode → ComplexAmplitudePhase
    carrier : (m : Mode) → Coordinate m

open ModalPhasorBank public

------------------------------------------------------------------------
-- Global phase may be observationally irrelevant while relative phase is
-- retained as the control coordinate.
------------------------------------------------------------------------

record RelativePhaseObservation : Set₁ where
  constructor relative-phase-observation
  field
    Phase : Set
    Observable : Set
    observeDifference : Phase → Phase → Observable

open RelativePhaseObservation public
