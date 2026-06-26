module DASHI.Physics.YangMills.O4RestorationLane where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives

record O4RestorationLane : Set₁ where
  field
    latticeSchwingersExist : Bool
    continuumSchwingersCandidated : Bool
    o4InvarianceRestored : Bool
    restorationErrorVanishes : Bool
    latticeSchwingersExistIsFalse : latticeSchwingersExist ≡ false
    continuumSchwingersCandidatedIsFalse :
      continuumSchwingersCandidated ≡ false
    o4InvarianceRestoredIsFalse : o4InvarianceRestored ≡ false
    restorationErrorVanishesIsFalse : restorationErrorVanishes ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalO4RestorationLane : O4RestorationLane
canonicalO4RestorationLane = record
  { latticeSchwingersExist = false
  ; continuumSchwingersCandidated = false
  ; o4InvarianceRestored = false
  ; restorationErrorVanishes = false
  ; latticeSchwingersExistIsFalse = refl
  ; continuumSchwingersCandidatedIsFalse = refl
  ; o4InvarianceRestoredIsFalse = refl
  ; restorationErrorVanishesIsFalse = refl
  ; noClayPromotion = refl
  }
