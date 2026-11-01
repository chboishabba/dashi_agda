module DASHI.Physics.ShiftPotentialCliffordMetric where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_)
import Data.Integer as Int
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.CliffordGate as CG
open import DASHI.Physics.ShiftPotentialBilinearBridge as SPBB
open import DASHI.Physics.ShiftPotentialQuadraticEnergy as SPQE
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Minimal Clifford-gate-facing metric package over the finite local bilinear
-- seam. This is still interface packaging only: it supplies the metric side
-- needed by the Clifford gate surface, but it does not supply a Clifford
-- algebra realization.

shiftScalarRingℤ : CG.RingLike ℤ
shiftScalarRingℤ =
  record
    { _+_ = Int._+_
    ; _*_ = Int._*_
    ; -_ = Int.-_
    ; 0# = + 0
    ; 1# = + 1
    }

shiftPotentialCliffordBilinear :
  CG.BilinearForm SPTI.ShiftPressurePoint ℤ
shiftPotentialCliffordBilinear =
  record
    { ⟪_,_⟫ = SPBB.shiftPotentialBilinear
    }

shiftPotentialCliffordDiagonalMatchesQuadratic :
  (s : SPTI.ShiftPressurePoint) →
  CG.BilinearForm.⟪_,_⟫ shiftPotentialCliffordBilinear s s
    ≡
  + (SPQE.shiftQuadraticEnergy s)
shiftPotentialCliffordDiagonalMatchesQuadratic =
  SPBB.shiftPotentialBilinearFormDiagonalMatchesQuadratic

record ShiftPotentialCliffordMetric : Set₁ where
  field
    scalarRing : CG.RingLike ℤ
    bilinearForm : CG.BilinearForm SPTI.ShiftPressurePoint ℤ
    diagonalMatchesQuadratic :
      (s : SPTI.ShiftPressurePoint) →
      CG.BilinearForm.⟪_,_⟫ bilinearForm s s ≡ + (SPQE.shiftQuadraticEnergy s)
    nonClaimBoundary : List String

shiftPotentialCliffordMetric :
  ShiftPotentialCliffordMetric
shiftPotentialCliffordMetric =
  record
    { scalarRing = shiftScalarRingℤ
    ; bilinearForm = shiftPotentialCliffordBilinear
    ; diagonalMatchesQuadratic = shiftPotentialCliffordDiagonalMatchesQuadratic
    ; nonClaimBoundary =
        "Finite local Clifford-metric package only"
        ∷ "Supplies only the metric side of the Clifford gate interface"
        ∷ "No Clifford algebra realization, spin group, or Dirac operator is constructed here"
        ∷ "Diagonal recovery is exact on the current finite carrier only"
        ∷ []
    }
