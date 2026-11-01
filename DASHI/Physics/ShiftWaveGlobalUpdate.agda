module DASHI.Physics.ShiftWaveGlobalUpdate where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteHelmholtzSurface as SDHS
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftSpatialLaplacian as SSL
open import DASHI.Physics.ShiftWaveRefinementHierarchy as SWRH

------------------------------------------------------------------------
-- Global synchronous one-pass update surface over the current finite fields.
--
-- This packages the Euler-style Schrödinger update as a whole-field operator
-- on both the coarse and refined carriers. It stays finite and theorem-thin:
-- no unitarity, no stability theorem, and no continuum PDE claim.

coarseGlobalUpdate :
  SSL.ShiftWaveField → SSL.ShiftWaveField
coarseGlobalUpdate ψ s =
  SDHS.fieldSchrodingerStep3 ψ s

fineGlobalUpdate :
  SWRH.ShiftWaveField5 → SWRH.ShiftWaveField5
fineGlobalUpdate ψ s =
  SDHS.fieldSchrodingerStep5 ψ s

LiftedGlobalUpdateCompatibility : Set
LiftedGlobalUpdateCompatibility =
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  fineGlobalUpdate (SWRH.liftField3to5 ψ) (SWRH.embed3to5 s)
    ≡
  coarseGlobalUpdate ψ s

liftedGlobalUpdateCompatibility : LiftedGlobalUpdateCompatibility
liftedGlobalUpdateCompatibility ψ SPTI.shiftStartPoint = refl
liftedGlobalUpdateCompatibility ψ SPTI.shiftNextPoint = refl
liftedGlobalUpdateCompatibility ψ SPTI.shiftHeldExitPoint = refl

record ShiftWaveGlobalUpdate : Setω where
  field
    coarseField : Set
    fineField : Set
    coarseUpdate :
      coarseField → coarseField
    fineUpdate :
      fineField → fineField
    liftCompatibility : Set
    nonClaimBoundary : List String

shiftWaveGlobalUpdate : ShiftWaveGlobalUpdate
shiftWaveGlobalUpdate =
  record
    { coarseField = SSL.ShiftWaveField
    ; fineField = SWRH.ShiftWaveField5
    ; coarseUpdate = coarseGlobalUpdate
    ; fineUpdate = fineGlobalUpdate
    ; liftCompatibility = LiftedGlobalUpdateCompatibility
    ; nonClaimBoundary =
        "Finite synchronous global-update package only"
        ∷ "updates are one-pass field maps induced by the current Euler-style Schrodinger step"
        ∷ "compatibility is only stated on lifted coarse fields at embedded coarse points"
        ∷ "No unitarity, stability, spectral convergence, or continuum PDE claim is implied"
        ∷ []
    }
