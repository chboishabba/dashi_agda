module DASHI.Physics.ShiftPotentialQuadraticEnergy where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Nat using (_≤_; _*_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using (≤-refl)

open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Finite scalar quadratic-energy package induced by the held potential on
-- the bounded three-point shift carrier.
--
-- This is intentionally not the full canonical quadratic-form lane. It is a
-- local finite-energy package that can later be related to that lane without
-- pretending the polarization / vector-space structure is already present.

shiftQuadraticEnergy :
  SPTI.ShiftPressurePoint →
  Nat
shiftQuadraticEnergy s =
  DDSI.shiftHeldPotential s * DDSI.shiftHeldPotential s

ShiftQuadraticDescentLaw : Set
ShiftQuadraticDescentLaw =
  (s : SPTI.ShiftPressurePoint) →
  shiftQuadraticEnergy (DDSI.shiftPressureAdvance s)
    ≤
  shiftQuadraticEnergy s

record ShiftPotentialQuadraticEnergy : Set where
  field
    potential :
      SPTI.ShiftPressurePoint → Nat
    energy :
      SPTI.ShiftPressurePoint → Nat
    energy-def :
      ∀ s → energy s ≡ potential s * potential s
    energy-descent :
      ∀ s →
        energy (DDSI.shiftPressureAdvance s)
          ≤
        energy s
    energy-zero-held :
      energy SPTI.shiftHeldExitPoint ≡ zero

shiftQuadraticEnergyDef :
  ∀ s →
  shiftQuadraticEnergy s ≡ DDSI.shiftHeldPotential s * DDSI.shiftHeldPotential s
shiftQuadraticEnergyDef s = refl

shiftQuadraticDescentWitness :
  ShiftQuadraticDescentLaw
shiftQuadraticDescentWitness SPTI.shiftStartPoint = s≤s z≤n
shiftQuadraticDescentWitness SPTI.shiftNextPoint = z≤n
shiftQuadraticDescentWitness SPTI.shiftHeldExitPoint = NatP.≤-refl

shiftQuadraticEnergyZeroHeld :
  shiftQuadraticEnergy SPTI.shiftHeldExitPoint ≡ zero
shiftQuadraticEnergyZeroHeld = refl

shiftPotentialQuadraticEnergy :
  ShiftPotentialQuadraticEnergy
shiftPotentialQuadraticEnergy =
  record
    { potential = DDSI.shiftHeldPotential
    ; energy = shiftQuadraticEnergy
    ; energy-def = shiftQuadraticEnergyDef
    ; energy-descent = shiftQuadraticDescentWitness
    ; energy-zero-held = shiftQuadraticEnergyZeroHeld
    }
