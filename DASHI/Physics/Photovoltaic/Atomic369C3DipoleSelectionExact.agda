module DASHI.Physics.Photovoltaic.Atomic369C3DipoleSelectionExact where

-- 2026-11-16: physical optical C3 selection as a conditional theorem.
-- Reuse the original atomic p-shell C3 action and symbolic character table.
-- This is *not* a theorem that allowed transitions are optically bright.
-- Full complex amplitude material, operator covariance, oscillator strengths
-- and Agda type-check acceptance are still source-paid gates.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Algebra.TriadicDepthOneCharacters as Char
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as Atomic

data False : Set where

composeEqualities : {A : Set} {a b c : A} ->
  a ≡ b -> b ≡ c -> a ≡ c
composeEqualities refl bc = bc

zeroPhaseNotPositive : Char.phase0 ≡ Char.phase1 -> False
zeroPhaseNotPositive ()

-- The crucial physical assumption is not just the abstract C3 carrier.
-- The optical transition is a linear amplitude over a representation
-- that separates *different phases* on every nonzero vector.
-- In an actual device this would be paid by a complex-Hilbert amplitude
-- and a verified covariant dipole operator on that same material.
record C3DipoleCovariant : Set₁ where
  field
    Amplitude : Set
    zero : Amplitude
    scalePhase : Char.C3Phase -> Amplitude -> Amplitude
    photonCharge : Char.C3Phase
    dipole : Atomic.MagneticState -> Atomic.MagneticState -> Amplitude

    opticalRotationCovariance :
      (initial final : Atomic.MagneticState) ->
      scalePhase (Atomic.rotationPhase final) (dipole initial final)
      ≡
      scalePhase
        (Char.multiplyPhase (Atomic.rotationPhase initial) photonCharge)
        (dipole initial final)

    phaseSeparation :
      (left right : Char.C3Phase) (a : Amplitude) ->
      (left ≡ right -> False) ->
      scalePhase left a ≡ scalePhase right a ->
      a ≡ zero

open C3DipoleCovariant public

forbiddenDipoleIsZero :
  (d : C3DipoleCovariant) ->
  (initial final : Atomic.MagneticState) ->
  ( Atomic.rotationPhase final
    ≡ Char.multiplyPhase (Atomic.rotationPhase initial) (photonCharge d)
    -> False ) ->
  dipole d initial final ≡ zero d
forbiddenDipoleIsZero d initial final mismatched =
  phaseSeparation d
    (Atomic.rotationPhase final)
    (Char.multiplyPhase (Atomic.rotationPhase initial) (photonCharge d))
    (dipole d initial final)
    mismatched
    (opticalRotationCovariance d initial final)

-- Concrete source-owned p-shell phase discrimination:
-- a charge +1 optical component cannot connect m=0 back to m=0.
positiveChargeNeutralToNeutralIsDark :
  (d : C3DipoleCovariant) ->
  photonCharge d ≡ Char.phase1 ->
  dipole d Atomic.mZero Atomic.mZero ≡ zero d
positiveChargeNeutralToNeutralIsDark d positivePhoton =
  forbiddenDipoleIsZero d Atomic.mZero Atomic.mZero
    (λ eq -> zeroPhaseNotPositive (composeEqualities eq positivePhoton))

-- A phase-allowed transition is NOT automatically nonzero:
-- the phase theorem supplies no lower bound on oscillator strength.
-- A material-specific dipole matrix and independent spectral evidence
-- must pay nonzero strength and charge collection as separate consumers.
record SameMaterialNonzeroOpticalPayment (d : C3DipoleCovariant) : Set where
  field
    initial final : Atomic.MagneticState
    allowedChargeEquality :
      Atomic.rotationPhase final
      ≡ Char.multiplyPhase (Atomic.rotationPhase initial) (photonCharge d)
    nonzeroStrength : dipole d initial final ≡ zero d -> False
