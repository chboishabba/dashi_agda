module DASHI.Physics.YangMills.BalabanSide4TranslationSymmetryExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact

subtract4SwapNegate : ∀ left right →
  subtract4 left right ≡ negate4 (subtract4 right left)
subtract4SwapNegate zeroᵢ zeroᵢ = refl
subtract4SwapNegate zeroᵢ (sucᵢ zeroᵢ) = refl
subtract4SwapNegate zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4SwapNegate zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl
subtract4SwapNegate (sucᵢ zeroᵢ) zeroᵢ = refl
subtract4SwapNegate (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) = refl
subtract4SwapNegate (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4SwapNegate (sucᵢ zeroᵢ)
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl
subtract4SwapNegate (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ = refl
subtract4SwapNegate (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) = refl
subtract4SwapNegate (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4SwapNegate (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl
subtract4SwapNegate (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ = refl
subtract4SwapNegate (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ zeroᵢ) = refl
subtract4SwapNegate (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4SwapNegate (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl

subtractSiteSwapNegate : ∀ left right →
  subtractSite4 left right ≡ negateSite4 (subtractSite4 right left)
subtractSiteSwapNegate
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  pair4Cong
    (subtract4SwapNegate l0 r0)
    (subtract4SwapNegate l1 r1)
    (subtract4SwapNegate l2 r2)
    (subtract4SwapNegate l3 r3)

side4TranslationSymmetryLevel : ProofLevel
side4TranslationSymmetryLevel = machineChecked
