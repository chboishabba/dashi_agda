module DASHI.Physics.ShiftPotentialQuadraticBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.ContractionQuadraticBridge as CQ
open import DASHI.Physics.ShiftPotentialQuadraticEnergy as SPQE
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Finite local bridge from the pressure-induced quadratic-energy surface to
-- the existing QuadraticOutput carrier used by the repo's quadratic lane.
--
-- This is intentionally bridge-only. It does not claim that pressure dynamics
-- has reconstructed the canonical contraction => quadratic theorem path.

shiftPotentialLyapunovWitness :
  CQ.LyapunovWitness
    SPTI.ShiftPressurePoint
    Nat
    SPQE.shiftQuadraticEnergy
shiftPotentialLyapunovWitness =
  record
    { potential = SPQE.shiftQuadraticEnergy
    ; potentialMatchesQuadratic = λ _ → refl
    }

shiftPotentialUniqueUpToScaleWitness :
  CQ.UniqueUpToScaleWitness
    SPTI.ShiftPressurePoint
    Nat
    SPQE.shiftQuadraticEnergy
shiftPotentialUniqueUpToScaleWitness =
  record
    { referenceQuadratic = SPQE.shiftQuadraticEnergy
    ; normalized = λ _ → refl
    }

shiftPotentialQuadraticOutput :
  CQ.QuadraticOutput
shiftPotentialQuadraticOutput =
  record
    { V = SPTI.ShiftPressurePoint
    ; Scalar = Nat
    ; B = λ s _ → SPQE.shiftQuadraticEnergy s
    ; Q = SPQE.shiftQuadraticEnergy
    ; Q-def = λ _ → refl
    ; lyapunovWitness = shiftPotentialLyapunovWitness
    ; uniqueUpToScaleWitness = shiftPotentialUniqueUpToScaleWitness
    }

shiftPotentialQuadraticMatchesEnergy :
  ∀ s →
  CQ.Q shiftPotentialQuadraticOutput s ≡ SPQE.shiftQuadraticEnergy s
shiftPotentialQuadraticMatchesEnergy s = refl

record ShiftPotentialQuadraticBridge : Set₁ where
  field
    energySurface :
      SPQE.ShiftPotentialQuadraticEnergy
    quadraticOutput :
      CQ.QuadraticOutput
    nonClaimBoundary :
      List String

shiftPotentialQuadraticBridge :
  ShiftPotentialQuadraticBridge
shiftPotentialQuadraticBridge =
  record
    { energySurface = SPQE.shiftPotentialQuadraticEnergy
    ; quadraticOutput = shiftPotentialQuadraticOutput
    ; nonClaimBoundary =
        "Finite local pressure-to-quadratic bridge only"
        ∷ "QuadraticOutput is packaged over the current three-point shift carrier"
        ∷ "The bilinear slot is a local diagonal placeholder matching the finite energy surface"
        ∷ "No claim is made that pressure dynamics reconstructs the canonical contraction=>quadratic theorem path"
        ∷ "No polarization, vector-space, or signature-forcing theorem is implied here"
        ∷ []
    }
