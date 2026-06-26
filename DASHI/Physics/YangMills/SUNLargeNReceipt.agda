module DASHI.Physics.YangMills.SUNLargeNReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives

record SUNLargeNReceipt : Set₁ where
  field
    sequenceDefined : Bool
    tHooftCouplingFixed : Bool
    observablesFamilyStable : Bool
    largeNLimitExists : Bool
    largeNGapTransfers : Bool
    sequenceDefinedIsTrue : sequenceDefined ≡ true
    tHooftCouplingFixedIsTrue : tHooftCouplingFixed ≡ true
    observablesFamilyStableIsFalse : observablesFamilyStable ≡ false
    largeNLimitExistsIsFalse : largeNLimitExists ≡ false
    largeNGapTransfersIsFalse : largeNGapTransfers ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalSUNLargeNReceipt : SUNLargeNReceipt
canonicalSUNLargeNReceipt = record
  { sequenceDefined = true
  ; tHooftCouplingFixed = true
  ; observablesFamilyStable = false
  ; largeNLimitExists = false
  ; largeNGapTransfers = false
  ; sequenceDefinedIsTrue = refl
  ; tHooftCouplingFixedIsTrue = refl
  ; observablesFamilyStableIsFalse = refl
  ; largeNLimitExistsIsFalse = refl
  ; largeNGapTransfersIsFalse = refl
  ; noClayPromotion = refl
  }
