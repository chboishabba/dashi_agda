module DASHI.Geometry.Gauge.SUNLane where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.Gauge.SUNPrimitives
open import DASHI.Geometry.Gauge.SpecialUnitaryCarrier
open import DASHI.Geometry.Gauge.SUNLieAlgebra
open import DASHI.Geometry.Gauge.SUNConnectionCurvature
open import DASHI.Geometry.Gauge.SUNRepresentation
open import DASHI.Geometry.Gauge.SUNCenter

record SUNLane (N : Nat) : Set₁ where
  field
    groupCarrier : SpecialUnitaryCarrier N
    lieAlgebra : SUNLieAlgebra N
    gaugeField : SUNGaugeField N
    representation : SUNRepresentation N
    centre : SUNCenter N
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalSUNLane : (N : Nat) → SUNLane N
canonicalSUNLane N = record
  { groupCarrier = canonicalSpecialUnitaryCarrier N
  ; lieAlgebra = canonicalSUNLieAlgebra N
  ; gaugeField = canonicalSUNGaugeField N
  ; representation = fundamentalRepresentation N
  ; centre = canonicalSUNCenter N
  ; noClayPromotion = refl
  }
