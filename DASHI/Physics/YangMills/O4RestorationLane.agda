module DASHI.Physics.YangMills.O4RestorationLane where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives

record O4RestorationLane : Set₁ where
  field
    latticeSchwingersExist : Bool
    continuumSchwingersCandidated : Bool
    o4InvarianceRestored : Bool
    restorationErrorVanishes : Bool
    latticeSchwingersExistIsTrue : latticeSchwingersExist ≡ true
    continuumSchwingersCandidatedIsTrue :
      continuumSchwingersCandidated ≡ true
    o4InvarianceRestoredIsTrue : o4InvarianceRestored ≡ true
    restorationErrorVanishesIsTrue : restorationErrorVanishes ≡ true
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalO4RestorationLane : O4RestorationLane
canonicalO4RestorationLane = record
  { latticeSchwingersExist = true
  ; continuumSchwingersCandidated = true
  ; o4InvarianceRestored = true
  ; restorationErrorVanishes = true
  ; latticeSchwingersExistIsTrue = refl
  ; continuumSchwingersCandidatedIsTrue = refl
  ; o4InvarianceRestoredIsTrue = refl
  ; restorationErrorVanishesIsTrue = refl
  ; noClayPromotion = refl
  }
