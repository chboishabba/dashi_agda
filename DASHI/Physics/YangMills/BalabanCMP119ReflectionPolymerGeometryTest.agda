{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119ReflectionPolymerGeometryTest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Agda.Builtin.Nat using (zero; suc)

open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanCMP119ReflectionPolymerGeometryExact as Cut

-- Period 4 = PeriodicBlock 3.  The first block is at time rank 0 and the
-- second at time rank 3, so the cut at rank 2 is genuinely crossed.
period4Time3 : Periodic.PeriodicBlock 3
period4Time3 =
  pair
    (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ)
    (pair zeroᵢ zeroᵢ)

mixedPeriod4Polymer : Periodic.PeriodicPolymer 3
mixedPeriod4Polymer = Periodic.zeroBlock ∷ period4Time3 ∷ []

mixedPeriod4Crosses :
  Cut.classifyPeriodicPolymerAtCut 2 mixedPeriod4Polymer
    ≡ Cut.crossingSupport
mixedPeriod4Crosses = refl

zeroPeriod4Positive :
  Cut.classifyPeriodicBlockAtCut 2 (Periodic.zeroBlock {n = 3})
    ≡ Cut.positiveSide
zeroPeriod4Positive = refl

end
