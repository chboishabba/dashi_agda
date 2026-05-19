module DASHI.Physics.ShiftPhaseTableInterference where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as SPWSI

------------------------------------------------------------------------
-- Finite phase-table interference layer.
--
-- This stays fully finite: no trig, no complex numbers, no PDEs. The point
-- is only to introduce a genuine pair-state interaction observable over the
-- structured phase-wave carrier.

data Phase4 : Set where
  φ0 φ1 φ2 φ3 : Phase4

phaseDifference4 : Phase4 → Phase4 → Phase4
phaseDifference4 φ0 φ0 = φ0
phaseDifference4 φ0 φ1 = φ3
phaseDifference4 φ0 φ2 = φ2
phaseDifference4 φ0 φ3 = φ1
phaseDifference4 φ1 φ0 = φ1
phaseDifference4 φ1 φ1 = φ0
phaseDifference4 φ1 φ2 = φ3
phaseDifference4 φ1 φ3 = φ2
phaseDifference4 φ2 φ0 = φ2
phaseDifference4 φ2 φ1 = φ1
phaseDifference4 φ2 φ2 = φ0
phaseDifference4 φ2 φ3 = φ3
phaseDifference4 φ3 φ0 = φ3
phaseDifference4 φ3 φ1 = φ2
phaseDifference4 φ3 φ2 = φ1
phaseDifference4 φ3 φ3 = φ0

cos4 : Phase4 → ℤ
cos4 φ0 = + 1
cos4 φ1 = + 0
cos4 φ2 = -[1+ 0 ]
cos4 φ3 = + 0

phaseKernel4 : Phase4 → Phase4 → ℤ
phaseKernel4 φ ψ =
  cos4 (phaseDifference4 φ ψ)

PhaseKernel4Symmetric : Set
PhaseKernel4Symmetric =
  (φ ψ : Phase4) →
  phaseKernel4 φ ψ ≡ phaseKernel4 ψ φ

phaseKernel4-symmetric : PhaseKernel4Symmetric
phaseKernel4-symmetric φ0 φ0 = refl
phaseKernel4-symmetric φ0 φ1 = refl
phaseKernel4-symmetric φ0 φ2 = refl
phaseKernel4-symmetric φ0 φ3 = refl
phaseKernel4-symmetric φ1 φ0 = refl
phaseKernel4-symmetric φ1 φ1 = refl
phaseKernel4-symmetric φ1 φ2 = refl
phaseKernel4-symmetric φ1 φ3 = refl
phaseKernel4-symmetric φ2 φ0 = refl
phaseKernel4-symmetric φ2 φ1 = refl
phaseKernel4-symmetric φ2 φ2 = refl
phaseKernel4-symmetric φ2 φ3 = refl
phaseKernel4-symmetric φ3 φ0 = refl
phaseKernel4-symmetric φ3 φ1 = refl
phaseKernel4-symmetric φ3 φ2 = refl
phaseKernel4-symmetric φ3 φ3 = refl

samePhaseConstructiveKernel :
  (φ : Phase4) →
  phaseKernel4 φ φ ≡ + 1
samePhaseConstructiveKernel φ0 = refl
samePhaseConstructiveKernel φ1 = refl
samePhaseConstructiveKernel φ2 = refl
samePhaseConstructiveKernel φ3 = refl

orthogonalPhaseNeutralKernel :
  phaseKernel4 φ0 φ1 ≡ + 0
orthogonalPhaseNeutralKernel = refl

oppositePhaseDestructiveKernel :
  phaseKernel4 φ0 φ2 ≡ -[1+ 0 ]
oppositePhaseDestructiveKernel = refl

phaseClass4 :
  SPWSI.ShiftWavePhaseState → Phase4
phaseClass4 w with SPWSI.shiftPhaseWavePhase w
... | zero = φ0
... | suc zero = φ1
... | suc (suc zero) = φ2
... | suc (suc (suc _)) = φ3

record ShiftWavePairState : Set where
  constructor mkShiftWavePairState
  field
    left : SPWSI.ShiftWavePhaseState
    right : SPWSI.ShiftWavePhaseState

advanceWavePairState :
  ShiftWavePairState → ShiftWavePairState
advanceWavePairState p =
  mkShiftWavePairState
    (SPWSI.advanceWavePhaseState (ShiftWavePairState.left p))
    (SPWSI.advanceWavePhaseState (ShiftWavePairState.right p))

shiftPhaseInteraction4 :
  SPWSI.ShiftWavePhaseState →
  SPWSI.ShiftWavePhaseState →
  ℤ
shiftPhaseInteraction4 w₁ w₂ =
  phaseKernel4 (phaseClass4 w₁) (phaseClass4 w₂)

interferenceIntensity4FromData :
  Nat → Phase4 → Nat → Phase4 → ℤ
interferenceIntensity4FromData A φ B ψ =
  (+ (A * A))
    +ℤ
  (+ (B * B))
    +ℤ
  (((+ 2) *ℤ (+ (A * B))) *ℤ phaseKernel4 φ ψ)

shiftInterferenceIntensity4 :
  SPWSI.ShiftWavePhaseState →
  SPWSI.ShiftWavePhaseState →
  ℤ
shiftInterferenceIntensity4 w₁ w₂ =
  interferenceIntensity4FromData
    (SPWSI.shiftPhaseWaveAmplitude w₁)
    (phaseClass4 w₁)
    (SPWSI.shiftPhaseWaveAmplitude w₂)
    (phaseClass4 w₂)

samePhaseConstructiveIntensityShape :
  (A B : Nat) →
  interferenceIntensity4FromData A φ0 B φ0
    ≡
  (+ (A * A))
    +ℤ
  (+ (B * B))
    +ℤ
  (((+ 2) *ℤ (+ (A * B))) *ℤ (+ 1))
samePhaseConstructiveIntensityShape A B = refl

orthogonalPhaseNeutralIntensityFormula :
  (A B : Nat) →
  interferenceIntensity4FromData A φ0 B φ1
    ≡
  (+ (A * A))
    +ℤ
  (+ (B * B))
    +ℤ
  (((+ 2) *ℤ (+ (A * B))) *ℤ (+ 0))
orthogonalPhaseNeutralIntensityFormula A B = refl

record ShiftPhaseTableInterference : Set₁ where
  field
    pairAdvance :
      ShiftWavePairState → ShiftWavePairState
    interactionKernel :
      SPWSI.ShiftWavePhaseState →
      SPWSI.ShiftWavePhaseState →
      ℤ
    interferenceIntensity :
      SPWSI.ShiftWavePhaseState →
      SPWSI.ShiftWavePhaseState →
      ℤ
    kernelSymmetric : PhaseKernel4Symmetric
    nonClaimBoundary : List String

shiftPhaseTableInterference :
  ShiftPhaseTableInterference
shiftPhaseTableInterference =
  record
    { pairAdvance = advanceWavePairState
    ; interactionKernel = shiftPhaseInteraction4
    ; interferenceIntensity = shiftInterferenceIntensity4
    ; kernelSymmetric = phaseKernel4-symmetric
    ; nonClaimBoundary =
        "Finite phase-table interference package only"
        ∷ "Phase interaction is a four-class table, not trig or analytic phase"
        ∷ "Interference intensity is a bounded pair-state observable on the current carrier"
        ∷ "Constructive, destructive, and orthogonal cases are finite table cases only"
        ∷ "No Hilbert-space, PDE, or continuum wave mechanics claim is implied"
        ∷ []
    }
