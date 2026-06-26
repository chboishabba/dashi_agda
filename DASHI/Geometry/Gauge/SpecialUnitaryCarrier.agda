module DASHI.Geometry.Gauge.SpecialUnitaryCarrier where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives

data SpecialUnitaryCarrierObligation : Set where
  needsComplexMatrixCarrier : SpecialUnitaryCarrierObligation
  needsDeterminantSemantics : SpecialUnitaryCarrierObligation
  needsUnitaryLawRealizer   : SpecialUnitaryCarrierObligation
  needsHaarMeasureReceipt   : SpecialUnitaryCarrierObligation

data SpecialUnitaryConcreteInstanceObligation : Set where
  su1ConcreteCarrierPending : SpecialUnitaryConcreteInstanceObligation
  su2ConcreteCarrierPending : SpecialUnitaryConcreteInstanceObligation
  su3ConcreteCarrierPending : SpecialUnitaryConcreteInstanceObligation

canonicalSpecialUnitaryCarrierObligations : List SpecialUnitaryCarrierObligation
canonicalSpecialUnitaryCarrierObligations =
  needsComplexMatrixCarrier
  ∷ needsDeterminantSemantics
  ∷ needsUnitaryLawRealizer
  ∷ needsHaarMeasureReceipt
  ∷ []

record SpecialUnitaryCarrier (N : Nat) : Set₁ where
  field
    unitaryLawHolds   : Bool
    specialLawHolds   : Bool
    unitaryLawIsTrue  : unitaryLawHolds ≡ true
    specialLawIsTrue  : specialLawHolds ≡ true
    openObligations   : List SpecialUnitaryCarrierObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalSpecialUnitaryCarrierObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalSpecialUnitaryCarrier : (N : Nat) → SpecialUnitaryCarrier N
canonicalSpecialUnitaryCarrier N = record
  { unitaryLawHolds = true
  ; specialLawHolds = true
  ; unitaryLawIsTrue = refl
  ; specialLawIsTrue = refl
  ; openObligations = canonicalSpecialUnitaryCarrierObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
