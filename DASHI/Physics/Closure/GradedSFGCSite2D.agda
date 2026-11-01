module DASHI.Physics.Closure.GradedSFGCSite2D where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.LegendrePrimeLaneCliffordBridge as LPB
open import DASHI.Physics.Closure.TriadicMatrixGenerationTheorem as TMG
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC

------------------------------------------------------------------------
-- Minimal graded witness surface over the existing phase-only SFGC carrier.
--
-- This module does not invent a new multiplication law. It packages the
-- concrete selected prime-lane Legendre table together with the canonical
-- triadic matrix bridge as a graded witness layer over the current carrier.

LaneIndex : Set
LaneIndex = LPB.SelectedPrimeLane

laneValue : LaneIndex → Nat
laneValue = LPB.selectedPrimeLaneToNat

canonicalCrossSign :
  LaneIndex →
  LaneIndex →
  LPB.Sign
canonicalCrossSign i j =
  LPB.selectedLegendreSignNat (laneValue i) (laneValue j)

record GradedSFGCSite2D : Set₁ where
  field
    site :
      SFGC.SFGCSite2D

    gradeLane :
      LaneIndex

    matrixBridge :
      TMG.TriadicMatrixGenerationTheorem

    legendreBridge :
      LPB.LegendreCliffordBridge

    crossSign :
      LaneIndex →
      LaneIndex →
      LPB.Sign

    crossDef :
      ∀ i j →
      crossSign i j ≡ LPB.selectedLegendreSignNat (laneValue i) (laneValue j)

canonicalGradedSFGCSite2D :
  GradedSFGCSite2D
canonicalGradedSFGCSite2D =
  record
    { site =
        SFGC.sfgcSite2D SPTI.shiftStartPoint SPTI.shiftStartPoint
    ; gradeLane =
        LPB.lane7
    ; matrixBridge =
        TMG.canonicalTriadicMatrixGenerationTheorem
    ; legendreBridge =
        LPB.canonicalLegendreCliffordBridge
    ; crossSign =
        canonicalCrossSign
    ; crossDef =
        λ i j → refl
    }
