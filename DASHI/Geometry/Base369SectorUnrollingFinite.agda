module DASHI.Geometry.Base369SectorUnrollingFinite where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exact finite radial profiles.
--
-- At ring index j, arc length is proportional to j.  The profile is the
-- finite object that is straightened into the familiar triangular picture.

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

sumNat : List Nat → Nat
sumNat [] = 0
sumNat (x ∷ xs) = x + sumNat xs

ringArcProfile : Nat → Nat → List Nat
ringArcProfile angleUnits zero = []
ringArcProfile angleUnits (suc rings) =
  ringArcProfile angleUnits rings ++
  ((angleUnits * rings) ∷ [])

finiteSectorAreaUnits : Nat → Nat → Nat
finiteSectorAreaUnits angleUnits rings =
  sumNat (ringArcProfile angleUnits rings)

threeRingProfile : ringArcProfile 2 3 ≡ 0 ∷ 2 ∷ 4 ∷ []
threeRingProfile = refl

threeRingAreaUnits : finiteSectorAreaUnits 2 3 ≡ 6
threeRingAreaUnits = refl

record RingArcSample : Set where
  constructor ringArcSample
  field
    angleUnits : Nat
    radiusIndex : Nat
    arcLengthUnits : Nat
    arcLengthIsLinear :
      arcLengthUnits ≡ angleUnits * radiusIndex

open RingArcSample public

canonicalRingArcSample : Nat → Nat → RingArcSample
canonicalRingArcSample angle radius =
  ringArcSample angle radius (angle * radius) refl

record FiniteSectorUnrollingReceipt : Set where
  constructor finiteSectorUnrollingReceipt
  field
    ringCount : Nat
    discreteAngleUnits : Nat
    arcProfile : List Nat
    arcProfileMatches :
      arcProfile ≡ ringArcProfile discreteAngleUnits ringCount
    accumulatedAreaUnits : Nat
    accumulatedAreaMatches :
      accumulatedAreaUnits ≡
      finiteSectorAreaUnits discreteAngleUnits ringCount
    finiteProfileChecked : Bool
    realIntegralPromoted : Bool
    realIntegralPromotedIsFalse : realIntegralPromoted ≡ false
    continuumAreaFormulaPromoted : Bool
    continuumAreaFormulaPromotedIsFalse :
      continuumAreaFormulaPromoted ≡ false
    boundary : String

canonicalThreeRingUnrollingReceipt : FiniteSectorUnrollingReceipt
canonicalThreeRingUnrollingReceipt =
  finiteSectorUnrollingReceipt
    3
    2
    (0 ∷ 2 ∷ 4 ∷ [])
    refl
    6
    refl
    true
    false
    refl
    false
    refl
    "The finite concentric-ring arc profile and accumulated units are exact. Scaling limits, real integration, and A = one-half theta r squared remain analytic bridge obligations."
