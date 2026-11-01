module DASHI.Physics.ShiftDiscreteActionPrinciple where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteContinuityCurrent as SDCC
open import DASHI.Physics.ShiftDiscreteHelmholtzSurface as SDHS
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftSpatialLaplacian as SSL
open import DASHI.Physics.ShiftWaveGlobalUpdate as SWGU

------------------------------------------------------------------------
-- Theorem-thin discrete action-principle surface over the current finite
-- wave update.
--
-- This does not claim a variational derivation. It only packages:
--   * a local finite action density = local energy + local current magnitude,
--   * the corresponding three-point action observable,
--   * the exact Euler-style update law already used by the current system.

coarseActionDensity :
  SSL.ShiftWaveField →
  SPTI.ShiftPressurePoint →
  ℤ
coarseActionDensity ψ s =
  SDCC.coarseLocalEnergy ψ s
    +ℤ
  SDCC.coarseLocalCurrentMagnitude ψ s

coarseActionObservable :
  SSL.ShiftWaveField →
  ℤ
coarseActionObservable ψ =
  coarseActionDensity ψ SPTI.shiftStartPoint
    +ℤ
  coarseActionDensity ψ SPTI.shiftNextPoint
    +ℤ
  coarseActionDensity ψ SPTI.shiftHeldExitPoint

CoarseActionDensityShape : Set
CoarseActionDensityShape =
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  coarseActionDensity ψ s
    ≡
  SDCC.coarseLocalEnergy ψ s
    +ℤ
  SDCC.coarseLocalCurrentMagnitude ψ s

coarseActionDensityShapeWitness :
  CoarseActionDensityShape
coarseActionDensityShapeWitness ψ s = refl

CoarseEulerUpdateLaw : Set
CoarseEulerUpdateLaw =
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  SWGU.coarseGlobalUpdate ψ s
    ≡
  SDWS.waveAdd
    (ψ s)
    (SDWS.mulI (SDHS.coarseHamiltonian ψ s))

coarseEulerUpdateWitness :
  CoarseEulerUpdateLaw
coarseEulerUpdateWitness ψ s = refl

record ShiftDiscreteActionPrinciple : Setω where
  field
    Field : Set
    localActionDensity :
      Field → SPTI.ShiftPressurePoint → ℤ
    actionObservable :
      Field → ℤ
    update :
      Field → Field
    actionDensityShape : Set
    updateLaw : Set
    nonClaimBoundary : List String

shiftDiscreteActionPrinciple :
  ShiftDiscreteActionPrinciple
shiftDiscreteActionPrinciple =
  record
    { Field = SSL.ShiftWaveField
    ; localActionDensity = coarseActionDensity
    ; actionObservable = coarseActionObservable
    ; update = SWGU.coarseGlobalUpdate
    ; actionDensityShape = CoarseActionDensityShape
    ; updateLaw = CoarseEulerUpdateLaw
    ; nonClaimBoundary =
        "Finite discrete action-principle package only"
        ∷ "local action density is an explicit finite observable: local energy + local current magnitude"
        ∷ "update law is the current Euler-style Schrodinger step on the three-point field"
        ∷ "No variational derivation, stationary-action theorem, or Noether theorem is implied"
        ∷ "No Hilbert-space, PDE, or continuum action claim is implied"
        ∷ []
    }
