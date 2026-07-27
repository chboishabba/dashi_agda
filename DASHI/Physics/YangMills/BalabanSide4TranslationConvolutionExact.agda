module DASHI.Physics.YangMills.BalabanSide4TranslationConvolutionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
  using (next4; previous4; shiftForward4; shiftBackward4)
open import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact

------------------------------------------------------------------------
-- Subtracting a translated centre translates the difference oppositely.
------------------------------------------------------------------------

subtract4RightNext : ∀ left right →
  subtract4 left (next4 right) ≡ previous4 (subtract4 left right)
subtract4RightNext zeroᵢ zeroᵢ = refl
subtract4RightNext (sucᵢ zeroᵢ) zeroᵢ = refl
subtract4RightNext (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ = refl
subtract4RightNext (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ = refl
subtract4RightNext zeroᵢ (sucᵢ zeroᵢ) = refl
subtract4RightNext (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) = refl
subtract4RightNext (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) = refl
subtract4RightNext (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ zeroᵢ) = refl
subtract4RightNext zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4RightNext (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4RightNext (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4RightNext (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4RightNext zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl
subtract4RightNext (sucᵢ zeroᵢ)
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl
subtract4RightNext (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl
subtract4RightNext (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl

subtract4RightPrevious : ∀ left right →
  subtract4 left (previous4 right) ≡ next4 (subtract4 left right)
subtract4RightPrevious zeroᵢ zeroᵢ = refl
subtract4RightPrevious (sucᵢ zeroᵢ) zeroᵢ = refl
subtract4RightPrevious (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ = refl
subtract4RightPrevious (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ = refl
subtract4RightPrevious zeroᵢ (sucᵢ zeroᵢ) = refl
subtract4RightPrevious (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) = refl
subtract4RightPrevious (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) = refl
subtract4RightPrevious (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ zeroᵢ) = refl
subtract4RightPrevious zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4RightPrevious (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4RightPrevious (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4RightPrevious (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4RightPrevious zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl
subtract4RightPrevious (sucᵢ zeroᵢ)
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl
subtract4RightPrevious (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl
subtract4RightPrevious (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl

subtractSiteRightForward : ∀ axis left right →
  subtractSite4 left (shiftForward4 axis right)
  ≡ shiftBackward4 axis (subtractSite4 left right)
subtractSiteRightForward zeroᵢ
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair value (subtract4 l1 r1))
    (pair (subtract4 l2 r2) (subtract4 l3 r3)))
    (subtract4RightNext l0 r0)
subtractSiteRightForward (sucᵢ zeroᵢ)
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) value)
    (pair (subtract4 l2 r2) (subtract4 l3 r3)))
    (subtract4RightNext l1 r1)
subtractSiteRightForward (sucᵢ (sucᵢ zeroᵢ))
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) (subtract4 l1 r1))
    (pair value (subtract4 l3 r3)))
    (subtract4RightNext l2 r2)
subtractSiteRightForward (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) (subtract4 l1 r1))
    (pair (subtract4 l2 r2) value))
    (subtract4RightNext l3 r3)

subtractSiteRightBackward : ∀ axis left right →
  subtractSite4 left (shiftBackward4 axis right)
  ≡ shiftForward4 axis (subtractSite4 left right)
subtractSiteRightBackward zeroᵢ
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair value (subtract4 l1 r1))
    (pair (subtract4 l2 r2) (subtract4 l3 r3)))
    (subtract4RightPrevious l0 r0)
subtractSiteRightBackward (sucᵢ zeroᵢ)
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) value)
    (pair (subtract4 l2 r2) (subtract4 l3 r3)))
    (subtract4RightPrevious l1 r1)
subtractSiteRightBackward (sucᵢ (sucᵢ zeroᵢ))
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) (subtract4 l1 r1))
    (pair value (subtract4 l3 r3)))
    (subtract4RightPrevious l2 r2)
subtractSiteRightBackward (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) (subtract4 l1 r1))
    (pair (subtract4 l2 r2) value))
    (subtract4RightPrevious l3 r3)

side4TranslationConvolutionLevel : ProofLevel
side4TranslationConvolutionLevel = machineChecked
