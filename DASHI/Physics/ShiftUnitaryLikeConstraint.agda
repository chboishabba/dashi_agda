module DASHI.Physics.ShiftUnitaryLikeConstraint where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

------------------------------------------------------------------------
-- Basis-level unitary-like constraints for the finite discrete-wave package.
--
-- The quarter-turn `mulI` preserves the norm of the four phase-basis states,
-- and four successive quarter-turns return those basis states exactly.
-- This is intentionally weaker than unitary evolution for the Euler-style
-- Schrödinger step.

waveNormSq : SDWS.DiscreteWave → ℤ
waveNormSq ψ =
  (SDWS.DiscreteWave.re ψ *ℤ SDWS.DiscreteWave.re ψ)
    +ℤ
  (SDWS.DiscreteWave.im ψ *ℤ SDWS.DiscreteWave.im ψ)

phaseBasisNormPreserving :
  (φ : SPTI4.Phase4) →
  waveNormSq (SDWS.mulI (SDWS.encodePhase4 φ))
    ≡
  waveNormSq (SDWS.encodePhase4 φ)
phaseBasisNormPreserving SPTI4.φ0 = refl
phaseBasisNormPreserving SPTI4.φ1 = refl
phaseBasisNormPreserving SPTI4.φ2 = refl
phaseBasisNormPreserving SPTI4.φ3 = refl

phaseStep4 : SDWS.DiscreteWave → SDWS.DiscreteWave
phaseStep4 ψ =
  SDWS.mulI
    (SDWS.mulI
      (SDWS.mulI
        (SDWS.mulI ψ)))

phaseStep4Identity :
  (φ : SPTI4.Phase4) →
  phaseStep4 (SDWS.encodePhase4 φ) ≡ SDWS.encodePhase4 φ
phaseStep4Identity SPTI4.φ0 = refl
phaseStep4Identity SPTI4.φ1 = refl
phaseStep4Identity SPTI4.φ2 = refl
phaseStep4Identity SPTI4.φ3 = refl

record ShiftUnitaryLikeConstraint : Set₁ where
  field
    normSq :
      SDWS.DiscreteWave → ℤ
    basisNormPreserving :
      (φ : SPTI4.Phase4) →
      normSq (SDWS.mulI (SDWS.encodePhase4 φ))
        ≡
      normSq (SDWS.encodePhase4 φ)
    phaseCycleIdentity :
      (φ : SPTI4.Phase4) →
      phaseStep4 (SDWS.encodePhase4 φ) ≡ SDWS.encodePhase4 φ
    nonClaimBoundary : List String

shiftUnitaryLikeConstraint : ShiftUnitaryLikeConstraint
shiftUnitaryLikeConstraint =
  record
    { normSq = waveNormSq
    ; basisNormPreserving = phaseBasisNormPreserving
    ; phaseCycleIdentity = phaseStep4Identity
    ; nonClaimBoundary =
        "Finite basis-level unitarity analogue only"
        ∷ "mulI preserves norm on the four phase-basis states"
        ∷ "four quarter-turns return each basis state exactly"
        ∷ "The Euler-style Schrodinger step is not claimed unitary"
        ∷ "No Hilbert-space or self-adjointness claim is implied"
        ∷ []
    }
