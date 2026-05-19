module DASHI.Physics.ShiftDiscreteWaveStep where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as SPWSI
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
open import DASHI.Physics.ShiftPotentialQuadraticEnergy as SPQE

------------------------------------------------------------------------
-- Finite discrete-wave algebra over the structured phase-wave carrier.
--
-- This is still below complex analysis: phase is encoded by a four-class
-- table and the wave is just an integer pair `(re , im)`. The point is to
-- make superposition and a Schrödinger-like update explicit without claiming
-- unitarity or a continuum equation.

record DiscreteWave : Set where
  constructor mkDiscreteWave
  field
    re : ℤ
    im : ℤ

waveAdd : DiscreteWave → DiscreteWave → DiscreteWave
waveAdd ψ χ =
  mkDiscreteWave
    (DiscreteWave.re ψ +ℤ DiscreteWave.re χ)
    (DiscreteWave.im ψ +ℤ DiscreteWave.im χ)

scaleWave : ℤ → DiscreteWave → DiscreteWave
scaleWave k ψ =
  mkDiscreteWave
    (k *ℤ DiscreteWave.re ψ)
    (k *ℤ DiscreteWave.im ψ)

mulI : DiscreteWave → DiscreteWave
mulI ψ =
  mkDiscreteWave
    (-[1+ 0 ] *ℤ DiscreteWave.im ψ)
    (DiscreteWave.re ψ)

encodePhase4 : SPTI4.Phase4 → DiscreteWave
encodePhase4 SPTI4.φ0 = mkDiscreteWave (+ 1) (+ 0)
encodePhase4 SPTI4.φ1 = mkDiscreteWave (+ 0) (+ 1)
encodePhase4 SPTI4.φ2 = mkDiscreteWave (-[1+ 0 ]) (+ 0)
encodePhase4 SPTI4.φ3 = mkDiscreteWave (+ 0) (-[1+ 0 ])

waveOfData : Nat → SPTI4.Phase4 → DiscreteWave
waveOfData A φ =
  scaleWave (+ A) (encodePhase4 φ)

discreteWaveOf :
  SPWSI.ShiftWavePhaseState → DiscreteWave
discreteWaveOf w =
  waveOfData
    (SPWSI.shiftPhaseWaveAmplitude w)
    (SPTI4.phaseClass4 w)

quarterTurnByMulI-φ0 :
  mulI (encodePhase4 SPTI4.φ0) ≡ encodePhase4 SPTI4.φ1
quarterTurnByMulI-φ0 = refl

quarterTurnByMulI-φ1 :
  mulI (encodePhase4 SPTI4.φ1) ≡ encodePhase4 SPTI4.φ2
quarterTurnByMulI-φ1 = refl

quarterTurnByMulI-φ2 :
  mulI (encodePhase4 SPTI4.φ2) ≡ encodePhase4 SPTI4.φ3
quarterTurnByMulI-φ2 = refl

quarterTurnByMulI-φ3 :
  mulI (encodePhase4 SPTI4.φ3) ≡ encodePhase4 SPTI4.φ0
quarterTurnByMulI-φ3 = refl

Hamiltonian : Set
Hamiltonian = DiscreteWave → DiscreteWave

shiftHamiltonian4 :
  SPWSI.ShiftWavePhaseState → Hamiltonian
shiftHamiltonian4 w ψ =
  scaleWave
    (+ (SPQE.shiftQuadraticEnergy (SPWSI.ShiftWavePhaseState.carrier w)))
    ψ

schrodingerStep :
  Hamiltonian → DiscreteWave → DiscreteWave
schrodingerStep H ψ =
  waveAdd ψ (mulI (H ψ))

shiftSchrodingerStep4 :
  SPWSI.ShiftWavePhaseState →
  DiscreteWave →
  DiscreteWave
shiftSchrodingerStep4 w =
  schrodingerStep (shiftHamiltonian4 w)

shiftStateIndexedSchrodingerStep4 :
  SPWSI.ShiftWavePhaseState →
  DiscreteWave
shiftStateIndexedSchrodingerStep4 w =
  shiftSchrodingerStep4 w (discreteWaveOf w)

record ShiftDiscreteWaveStep : Set₁ where
  field
    waveOf :
      SPWSI.ShiftWavePhaseState → DiscreteWave
    superposition :
      DiscreteWave → DiscreteWave → DiscreteWave
    hamiltonian :
      SPWSI.ShiftWavePhaseState → Hamiltonian
    step :
      SPWSI.ShiftWavePhaseState → DiscreteWave → DiscreteWave
    nonClaimBoundary : List String

shiftDiscreteWaveStep :
  ShiftDiscreteWaveStep
shiftDiscreteWaveStep =
  record
    { waveOf = discreteWaveOf
    ; superposition = waveAdd
    ; hamiltonian = shiftHamiltonian4
    ; step = shiftSchrodingerStep4
    ; nonClaimBoundary =
        "Finite discrete-wave package only"
        ∷ "Wave values are integer pairs, not complex amplitudes"
        ∷ "Phase is encoded by a four-class table rather than analytic phase"
        ∷ "Schrodinger-like step is Euler-style finite packaging only"
        ∷ "No unitarity, self-adjointness, Hilbert space, or continuum PDE claim is implied"
        ∷ []
    }
