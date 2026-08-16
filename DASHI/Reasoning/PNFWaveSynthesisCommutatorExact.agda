module DASHI.Reasoning.PNFWaveSynthesisCommutatorExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Make the synthesis/transport commutator explicit on the repository's
-- existing finite DiscreteWave carrier. In this concrete wave realization,
-- synthesis is additive superposition:
--
--   Sigma(x,y) = x + y.
--
-- For a transport T define
--
--   delta_Sigma(x,y) = Sigma(Tx,Ty) - T(Sigma(x,y)).
--
-- Any additive transport has zero defect. The existing state-indexed finite
-- Schrodinger-style step is additive because its Hamiltonian is scalar
-- multiplication and multiplication by i is additive. Hence this existing
-- finite wave step satisfies the commuting synthesis square exactly.
--
-- This is a finite integer-pair theorem only. It does not promote the wave
-- carrier to analytic Hilbert-space, quantum, psychological or continuum
-- authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _*_)

import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as SPWSI
import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Physics.ShiftPotentialQuadraticEnergy as Energy

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; solve)

zeroWave : Wave.DiscreteWave
zeroWave = Wave.mkDiscreteWave (+ 0) (+ 0)

waveNeg : Wave.DiscreteWave → Wave.DiscreteWave
waveNeg = Wave.scaleWave (- (+ 1))

waveSub : Wave.DiscreteWave → Wave.DiscreteWave → Wave.DiscreteWave
waveSub left right = Wave.waveAdd left (waveNeg right)

waveExtensional :
  (left right : Wave.DiscreteWave) →
  Wave.DiscreteWave.re left ≡ Wave.DiscreteWave.re right →
  Wave.DiscreteWave.im left ≡ Wave.DiscreteWave.im right →
  left ≡ right
waveExtensional
  (Wave.mkDiscreteWave leftRe leftIm)
  (Wave.mkDiscreteWave rightRe rightIm)
  refl refl = refl

waveSubSelf :
  (wave : Wave.DiscreteWave) →
  waveSub wave wave ≡ zeroWave
waveSubSelf (Wave.mkDiscreteWave real imag) =
  waveExtensional
    (waveSub
      (Wave.mkDiscreteWave real imag)
      (Wave.mkDiscreteWave real imag))
    zeroWave
    (RingZ.solve 1
      (λ x →
        ( x ⊕ (Κ (- (+ 1)) ⊗ x)
        , Κ (+ 0)))
      refl real)
    (RingZ.solve 1
      (λ x →
        ( x ⊕ (Κ (- (+ 1)) ⊗ x)
        , Κ (+ 0)))
      refl imag)

record AdditiveWaveTransport : Set₁ where
  constructor additiveWaveTransport
  field
    transport : Wave.DiscreteWave → Wave.DiscreteWave
    preservesSuperposition :
      (left right : Wave.DiscreteWave) →
      transport (Wave.waveAdd left right)
      ≡ Wave.waveAdd (transport left) (transport right)

open AdditiveWaveTransport public

synthesisTransportDefect :
  (Wave.DiscreteWave → Wave.DiscreteWave) →
  Wave.DiscreteWave → Wave.DiscreteWave →
  Wave.DiscreteWave
synthesisTransportDefect transport left right =
  waveSub
    (Wave.waveAdd (transport left) (transport right))
    (transport (Wave.waveAdd left right))

additiveTransportHasZeroSynthesisDefect :
  (transportSurface : AdditiveWaveTransport) →
  (left right : Wave.DiscreteWave) →
  synthesisTransportDefect
    (transport transportSurface) left right
  ≡ zeroWave
additiveTransportHasZeroSynthesisDefect transportSurface left right
  rewrite preservesSuperposition transportSurface left right =
  waveSubSelf
    (Wave.waveAdd
      (transport transportSurface left)
      (transport transportSurface right))

scaleWavePreservesSuperposition :
  (scalar : ℤ) →
  (left right : Wave.DiscreteWave) →
  Wave.scaleWave scalar (Wave.waveAdd left right)
  ≡ Wave.waveAdd
      (Wave.scaleWave scalar left)
      (Wave.scaleWave scalar right)
scaleWavePreservesSuperposition scalar
  (Wave.mkDiscreteWave leftRe leftIm)
  (Wave.mkDiscreteWave rightRe rightIm) =
  waveExtensional
    (Wave.scaleWave scalar
      (Wave.waveAdd
        (Wave.mkDiscreteWave leftRe leftIm)
        (Wave.mkDiscreteWave rightRe rightIm)))
    (Wave.waveAdd
      (Wave.scaleWave scalar
        (Wave.mkDiscreteWave leftRe leftIm))
      (Wave.scaleWave scalar
        (Wave.mkDiscreteWave rightRe rightIm)))
    (RingZ.solve 3
      (λ k x y →
        ( k ⊗ (x ⊕ y)
        , (k ⊗ x) ⊕ (k ⊗ y)))
      refl scalar leftRe rightRe)
    (RingZ.solve 3
      (λ k x y →
        ( k ⊗ (x ⊕ y)
        , (k ⊗ x) ⊕ (k ⊗ y)))
      refl scalar leftIm rightIm)

mulIPreservesSuperposition :
  (left right : Wave.DiscreteWave) →
  Wave.mulI (Wave.waveAdd left right)
  ≡ Wave.waveAdd (Wave.mulI left) (Wave.mulI right)
mulIPreservesSuperposition
  (Wave.mkDiscreteWave leftRe leftIm)
  (Wave.mkDiscreteWave rightRe rightIm) =
  waveExtensional
    (Wave.mulI
      (Wave.waveAdd
        (Wave.mkDiscreteWave leftRe leftIm)
        (Wave.mkDiscreteWave rightRe rightIm)))
    (Wave.waveAdd
      (Wave.mulI (Wave.mkDiscreteWave leftRe leftIm))
      (Wave.mulI (Wave.mkDiscreteWave rightRe rightIm)))
    (RingZ.solve 2
      (λ x y →
        ( Κ (- (+ 1)) ⊗ (x ⊕ y)
        , (Κ (- (+ 1)) ⊗ x) ⊕ (Κ (- (+ 1)) ⊗ y)))
      refl leftIm rightIm)
    refl

waveAddMedial :
  (a b c d : Wave.DiscreteWave) →
  Wave.waveAdd (Wave.waveAdd a b) (Wave.waveAdd c d)
  ≡ Wave.waveAdd (Wave.waveAdd a c) (Wave.waveAdd b d)
waveAddMedial
  (Wave.mkDiscreteWave ar ai)
  (Wave.mkDiscreteWave br bi)
  (Wave.mkDiscreteWave cr ci)
  (Wave.mkDiscreteWave dr di) =
  waveExtensional
    (Wave.waveAdd
      (Wave.waveAdd
        (Wave.mkDiscreteWave ar ai)
        (Wave.mkDiscreteWave br bi))
      (Wave.waveAdd
        (Wave.mkDiscreteWave cr ci)
        (Wave.mkDiscreteWave dr di)))
    (Wave.waveAdd
      (Wave.waveAdd
        (Wave.mkDiscreteWave ar ai)
        (Wave.mkDiscreteWave cr ci))
      (Wave.waveAdd
        (Wave.mkDiscreteWave br bi)
        (Wave.mkDiscreteWave dr di)))
    (RingZ.solve 4
      (λ a b c d →
        ( (a ⊕ b) ⊕ (c ⊕ d)
        , (a ⊕ c) ⊕ (b ⊕ d)))
      refl ar br cr dr)
    (RingZ.solve 4
      (λ a b c d →
        ( (a ⊕ b) ⊕ (c ⊕ d)
        , (a ⊕ c) ⊕ (b ⊕ d)))
      refl ai bi ci di)

record AdditiveHamiltonian (H : Wave.Hamiltonian) : Set where
  constructor additiveHamiltonian
  field
    hamiltonianAdditive :
      (left right : Wave.DiscreteWave) →
      H (Wave.waveAdd left right)
      ≡ Wave.waveAdd (H left) (H right)

open AdditiveHamiltonian public

schrodingerStepPreservesSuperposition :
  (H : Wave.Hamiltonian) →
  AdditiveHamiltonian H →
  (left right : Wave.DiscreteWave) →
  Wave.schrodingerStep H (Wave.waveAdd left right)
  ≡ Wave.waveAdd
      (Wave.schrodingerStep H left)
      (Wave.schrodingerStep H right)
schrodingerStepPreservesSuperposition H additiveH left right
  rewrite hamiltonianAdditive additiveH left right
        | mulIPreservesSuperposition (H left) (H right) =
  waveAddMedial left right (Wave.mulI (H left)) (Wave.mulI (H right))

shiftHamiltonianIsAdditive :
  (state : SPWSI.ShiftWavePhaseState) →
  AdditiveHamiltonian (Wave.shiftHamiltonian4 state)
shiftHamiltonianIsAdditive state =
  additiveHamiltonian
    (scaleWavePreservesSuperposition
      (+ (Energy.shiftQuadraticEnergy
        (SPWSI.ShiftWavePhaseState.carrier state))))

shiftStepIsAdditive :
  (state : SPWSI.ShiftWavePhaseState) →
  AdditiveWaveTransport
shiftStepIsAdditive state =
  additiveWaveTransport
    (Wave.shiftSchrodingerStep4 state)
    (schrodingerStepPreservesSuperposition
      (Wave.shiftHamiltonian4 state)
      (shiftHamiltonianIsAdditive state))

shiftStepSynthesisDefectIsZero :
  (state : SPWSI.ShiftWavePhaseState) →
  (left right : Wave.DiscreteWave) →
  synthesisTransportDefect
    (Wave.shiftSchrodingerStep4 state)
    left right
  ≡ zeroWave
shiftStepSynthesisDefectIsZero state =
  additiveTransportHasZeroSynthesisDefect (shiftStepIsAdditive state)

record PNFWaveSynthesisCommutatorBoundary : Set where
  field
    finiteWaveCommutatorConstructed : Bool
    finiteWaveCommutatorConstructedIsTrue :
      finiteWaveCommutatorConstructed ≡ true

    existingShiftStepHasZeroAdditiveSynthesisDefect : Bool
    existingShiftStepHasZeroAdditiveSynthesisDefectIsTrue :
      existingShiftStepHasZeroAdditiveSynthesisDefect ≡ true

    everyPNFSynthesisRuleIdentifiedWithWaveAddition : Bool
    everyPNFSynthesisRuleIdentifiedWithWaveAdditionIsFalse :
      everyPNFSynthesisRuleIdentifiedWithWaveAddition ≡ false

    zeroDefectPromotedToEmpiricalHealthClaim : Bool
    zeroDefectPromotedToEmpiricalHealthClaimIsFalse :
      zeroDefectPromotedToEmpiricalHealthClaim ≡ false

canonicalPNFWaveSynthesisCommutatorBoundary :
  PNFWaveSynthesisCommutatorBoundary
canonicalPNFWaveSynthesisCommutatorBoundary =
  record
    { finiteWaveCommutatorConstructed = true
    ; finiteWaveCommutatorConstructedIsTrue = refl
    ; existingShiftStepHasZeroAdditiveSynthesisDefect = true
    ; existingShiftStepHasZeroAdditiveSynthesisDefectIsTrue = refl
    ; everyPNFSynthesisRuleIdentifiedWithWaveAddition = false
    ; everyPNFSynthesisRuleIdentifiedWithWaveAdditionIsFalse = refl
    ; zeroDefectPromotedToEmpiricalHealthClaim = false
    ; zeroDefectPromotedToEmpiricalHealthClaimIsFalse = refl
    }
