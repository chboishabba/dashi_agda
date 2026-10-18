{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularEReflectionSupportCutTest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Agda.Builtin.Nat using (zero; suc)

open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanCMP119ReflectionPolymerGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP119RegularEReflectionSupportCutExact as Cut

period4Time3 : Periodic.PeriodicBlock 3
period4Time3 =
  pair
    (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ)
    (pair zeroᵢ zeroᵢ)

componentSupport : Bool → Periodic.PeriodicPolymer 3
componentSupport false = Periodic.zeroBlock ∷ []
componentSupport true = Periodic.zeroBlock ∷ period4Time3 ∷ []

positiveComponentClassifiesPositive :
  Cut.classifyRegularEComponentAtCut componentSupport 2 false
    ≡ Geometry.positiveOnly
positiveComponentClassifiesPositive = refl

mixedComponentClassifiesCrossing :
  Cut.classifyRegularEComponentAtCut componentSupport 2 true
    ≡ Geometry.crossingSupport
mixedComponentClassifiesCrossing = refl
