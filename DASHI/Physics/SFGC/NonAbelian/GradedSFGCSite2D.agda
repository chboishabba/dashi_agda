module DASHI.Physics.SFGC.NonAbelian.GradedSFGCSite2D where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.LegendrePrimeLaneCliffordBridge as LPB
open import DASHI.Physics.Closure.TriadicMatrixGenerationTheorem as TMG

------------------------------------------------------------------------
-- Concrete graded witness over the selected 7/11/13 prime lanes.
--
-- This is a finite witness layer: it packages the selected lane triple,
-- the canonical Legendre sign table, and the existing triadic matrix bridge.
-- It does not claim a quotient theorem or a carrier-level multiplication law.

data WeakLane : Set where
  lane7 lane11 lane13 : WeakLane

laneVal : WeakLane → Nat
laneVal lane7 = 7
laneVal lane11 = 11
laneVal lane13 = 13

crossingSign : WeakLane → WeakLane → LPB.Sign
crossingSign lane7 lane7 = LPB.pos
crossingSign lane7 lane11 = LPB.neg
crossingSign lane7 lane13 = LPB.neg
crossingSign lane11 lane7 = LPB.neg
crossingSign lane11 lane11 = LPB.pos
crossingSign lane11 lane13 = LPB.neg
crossingSign lane13 lane7 = LPB.neg
crossingSign lane13 lane11 = LPB.neg
crossingSign lane13 lane13 = LPB.pos

record GradedSFGCSite2DWitness : Set₁ where
  field
    gradeLane :
      WeakLane

    laneValue :
      WeakLane → Nat

    laneValueIsCanonical :
      laneValue ≡ laneVal

    matrixBridge :
      TMG.TriadicMatrixGenerationTheorem

    legendreBridge :
      LPB.LegendreCliffordBridge

    crossSign :
      WeakLane → WeakLane → LPB.Sign

    crossDef :
      ∀ i j →
      crossSign i j ≡ crossingSign i j

canonicalGradedSFGCSite2DWitness :
  GradedSFGCSite2DWitness
canonicalGradedSFGCSite2DWitness =
  record
    { gradeLane =
        lane7
    ; laneValue =
        laneVal
    ; laneValueIsCanonical =
        refl
    ; matrixBridge =
        TMG.canonicalTriadicMatrixGenerationTheorem
    ; legendreBridge =
        LPB.canonicalLegendreCliffordBridge
    ; crossSign =
        crossingSign
    ; crossDef =
        λ _ _ → refl
    }

open GradedSFGCSite2DWitness public
