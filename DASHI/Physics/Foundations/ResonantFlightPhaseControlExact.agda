module DASHI.Physics.Foundations.ResonantFlightPhaseControlExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Human-powered resonant flapping flight:
-- control deforms a periodic mode rather than prescribing every joint
-- position directly.
------------------------------------------------------------------------

record HarmonicCoordinate : Set₁ where
  constructor harmonic-coordinate
  field
    Amplitude : Set
    Phase : Set
    amplitude : Amplitude
    phase : Phase

open HarmonicCoordinate public

record RelativePhaseLayer : Set₁ where
  constructor relative-phase-layer
  field
    Phase : Set
    _⊖_ : Phase → Phase → Phase

open RelativePhaseLayer public

relativePhase :
  (R : RelativePhaseLayer) →
  RelativePhaseLayer.Phase R →
  RelativePhaseLayer.Phase R →
  RelativePhaseLayer.Phase R
relativePhase R = RelativePhaseLayer._⊖_ R

data WingDOF : Set where
  flap pitch fold twist span : WingDOF

record WingbeatMode : Set₁ where
  constructor wingbeat-mode
  field
    Coordinate : WingDOF → Set
    baseline : (d : WingDOF) → Coordinate d

open WingbeatMode public

record CyclicControl (PilotInput : Set) (W : WingbeatMode) : Set₁ where
  constructor cyclic-control
  field
    controlled : PilotInput → (d : WingDOF) → Coordinate W d
    neutral : PilotInput
    neutral-preserves-baseline :
      (d : WingDOF) → controlled neutral d ≡ baseline W d

open CyclicControl public

record LeftRightCyclicControl
  (PilotInput : Set)
  (W : WingbeatMode) : Set₁ where
  constructor left-right-cyclic-control
  field
    left right : PilotInput → (d : WingDOF) → Coordinate W d
    neutral : PilotInput
    neutral-left :
      (d : WingDOF) → left neutral d ≡ baseline W d
    neutral-right :
      (d : WingDOF) → right neutral d ≡ baseline W d

open LeftRightCyclicControl public

------------------------------------------------------------------------
-- Swashplate/cyclic analogy:
-- pilot commands alter the phase-indexed mode map, not an instantaneous
-- hard position prescription.
------------------------------------------------------------------------

record PhaseIndexedTrajectory : Set₁ where
  constructor phase-indexed-trajectory
  field
    Phase : Set
    JointState : Set
    trajectory : Phase → JointState

open PhaseIndexedTrajectory public

record CyclicModeDeformation
  (PilotInput : Set)
  (T : PhaseIndexedTrajectory) : Set₁ where
  constructor cyclic-mode-deformation
  field
    deformed : PilotInput → Phase T → JointState T
    neutral : PilotInput
    neutral-is-natural :
      (φ : Phase T) →
      deformed neutral φ ≡ trajectory T φ

open CyclicModeDeformation public

------------------------------------------------------------------------
-- The desired control invariant: neutral control leaves the mechanically
-- preferred periodic orbit unchanged.
------------------------------------------------------------------------

neutralModeIsFixed :
  {PilotInput : Set} →
  {T : PhaseIndexedTrajectory} →
  (C : CyclicModeDeformation PilotInput T) →
  (φ : Phase T) →
  deformed C (CyclicModeDeformation.neutral C) φ ≡ trajectory T φ
neutralModeIsFixed C = CyclicModeDeformation.neutral-is-natural C
