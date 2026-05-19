module DASHI.Physics.ShiftPotentialBilinearBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Clifford.SpinFromSignature as CG
open import DASHI.Physics.ShiftPotentialQuadraticEnergy as SPQE
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Finite bilinear-style handoff for the pressure-induced quadratic energy.
--
-- This is not a full polarization theorem because the shift pressure carrier
-- is not being presented here as an additive space. Instead, we expose one
-- explicit symmetric pair form whose diagonal recovers the finite quadratic
-- energy exactly on the current carrier.

shiftPotentialBilinear :
  SPTI.ShiftPressurePoint →
  SPTI.ShiftPressurePoint →
  ℤ
shiftPotentialBilinear SPTI.shiftStartPoint SPTI.shiftStartPoint = + 4
shiftPotentialBilinear SPTI.shiftStartPoint SPTI.shiftNextPoint = + 0
shiftPotentialBilinear SPTI.shiftStartPoint SPTI.shiftHeldExitPoint = + 0
shiftPotentialBilinear SPTI.shiftNextPoint SPTI.shiftStartPoint = + 0
shiftPotentialBilinear SPTI.shiftNextPoint SPTI.shiftNextPoint = + 1
shiftPotentialBilinear SPTI.shiftNextPoint SPTI.shiftHeldExitPoint = + 0
shiftPotentialBilinear SPTI.shiftHeldExitPoint SPTI.shiftStartPoint = + 0
shiftPotentialBilinear SPTI.shiftHeldExitPoint SPTI.shiftNextPoint = + 0
shiftPotentialBilinear SPTI.shiftHeldExitPoint SPTI.shiftHeldExitPoint = + 0

ShiftPotentialBilinearSymmetric : Set
ShiftPotentialBilinearSymmetric =
  (x y : SPTI.ShiftPressurePoint) →
  shiftPotentialBilinear x y ≡ shiftPotentialBilinear y x

shiftPotentialBilinearSymmetric :
  ShiftPotentialBilinearSymmetric
shiftPotentialBilinearSymmetric SPTI.shiftStartPoint SPTI.shiftStartPoint = refl
shiftPotentialBilinearSymmetric SPTI.shiftStartPoint SPTI.shiftNextPoint = refl
shiftPotentialBilinearSymmetric SPTI.shiftStartPoint SPTI.shiftHeldExitPoint = refl
shiftPotentialBilinearSymmetric SPTI.shiftNextPoint SPTI.shiftStartPoint = refl
shiftPotentialBilinearSymmetric SPTI.shiftNextPoint SPTI.shiftNextPoint = refl
shiftPotentialBilinearSymmetric SPTI.shiftNextPoint SPTI.shiftHeldExitPoint = refl
shiftPotentialBilinearSymmetric SPTI.shiftHeldExitPoint SPTI.shiftStartPoint = refl
shiftPotentialBilinearSymmetric SPTI.shiftHeldExitPoint SPTI.shiftNextPoint = refl
shiftPotentialBilinearSymmetric SPTI.shiftHeldExitPoint SPTI.shiftHeldExitPoint = refl

shiftPotentialBilinearDiagonalMatchesQuadratic :
  (s : SPTI.ShiftPressurePoint) →
  shiftPotentialBilinear s s ≡ + (SPQE.shiftQuadraticEnergy s)
shiftPotentialBilinearDiagonalMatchesQuadratic SPTI.shiftStartPoint = refl
shiftPotentialBilinearDiagonalMatchesQuadratic SPTI.shiftNextPoint = refl
shiftPotentialBilinearDiagonalMatchesQuadratic SPTI.shiftHeldExitPoint = refl

shiftPotentialBilinearForm : CG.BilinearForm
shiftPotentialBilinearForm =
  record
    { V = SPTI.ShiftPressurePoint
    ; g = shiftPotentialBilinear
    }

shiftPotentialBilinearFormDiagonalMatchesQuadratic :
  (s : SPTI.ShiftPressurePoint) →
  CG.g shiftPotentialBilinearForm s s ≡ + (SPQE.shiftQuadraticEnergy s)
shiftPotentialBilinearFormDiagonalMatchesQuadratic =
  shiftPotentialBilinearDiagonalMatchesQuadratic

record ShiftPotentialBilinearBridge : Set₁ where
  field
    bilinearForm : CG.BilinearForm
    symmetric : ShiftPotentialBilinearSymmetric
    nonClaimBoundary : List String

shiftPotentialBilinearBridge :
  ShiftPotentialBilinearBridge
shiftPotentialBilinearBridge =
  record
    { bilinearForm = shiftPotentialBilinearForm
    ; symmetric = shiftPotentialBilinearSymmetric
    ; nonClaimBoundary =
        "Finite local bilinear-style bridge only"
        ∷ "The shift carrier is not promoted here to a full additive or vector-space object"
        ∷ "diagonalMatchesQuadratic is exact on the current finite carrier"
        ∷ "No full polarization theorem, signature forcing, or Clifford realization is implied here"
        ∷ []
    }
