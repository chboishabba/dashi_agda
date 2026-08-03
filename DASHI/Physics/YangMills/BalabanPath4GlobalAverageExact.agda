module DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational; sumRationalCong; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumSwap)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
  using (siteSum4; siteSumAsCoordinates)

quarter2 quarter3 quarter4 oneTwoFiftySix : ℚ
quarter2 = quarter * quarter
quarter3 = quarter * quarter2
quarter4 = quarter * quarter3
oneTwoFiftySix = + 1 / 256

sum0 : SiteField side4 →
  CyclicIndex four → CyclicIndex four → CyclicIndex four → ℚ
sum0 field x1 x2 x3 =
  sumRational (allCyclicIndices four) (λ x0 →
    field (pair (pair x0 x1) (pair x2 x3)))

sum10 : SiteField side4 → CyclicIndex four → CyclicIndex four → ℚ
sum10 field x2 x3 =
  sumRational (allCyclicIndices four) (λ x1 → sum0 field x1 x2 x3)

sum210 : SiteField side4 → CyclicIndex four → ℚ
sum210 field x3 =
  sumRational (allCyclicIndices four) (λ x2 → sum10 field x2 x3)

reverseSiteSum : SiteField side4 → ℚ
reverseSiteSum field =
  sumRational (allCyclicIndices four) (sum210 field)

average0Explicit : ∀ field x0 x1 x2 x3 →
  average0 field (pair (pair x0 x1) (pair x2 x3))
  ≡ quarter * sum0 field x1 x2 x3
average0Explicit field x0 x1 x2 x3 = refl

average01Explicit : ∀ field x0 x1 x2 x3 →
  average01 field (pair (pair x0 x1) (pair x2 x3))
  ≡ quarter2 * sum10 field x2 x3
average01Explicit field x0 x1 x2 x3 =
  trans
    (cong (quarter *_)
      (sumRationalCong (allCyclicIndices four) _ _
        (λ coordinate →
          average0Explicit field x0 coordinate x2 x3)))
    (trans
      (cong (quarter *_)
        (sumRationalScale quarter (allCyclicIndices four)
          (λ coordinate → sum0 field coordinate x2 x3)))
      (ℚRing.solve-∀))

average012Explicit : ∀ field x0 x1 x2 x3 →
  average012 field (pair (pair x0 x1) (pair x2 x3))
  ≡ quarter3 * sum210 field x3
average012Explicit field x0 x1 x2 x3 =
  trans
    (cong (quarter *_)
      (sumRationalCong (allCyclicIndices four) _ _
        (λ coordinate →
          average01Explicit field x0 x1 coordinate x3)))
    (trans
      (cong (quarter *_)
        (sumRationalScale quarter2 (allCyclicIndices four)
          (λ coordinate → sum10 field coordinate x3)))
      (ℚRing.solve-∀))

average0123Explicit : ∀ field x0 x1 x2 x3 →
  average0123 field (pair (pair x0 x1) (pair x2 x3))
  ≡ quarter4 * reverseSiteSum field
average0123Explicit field x0 x1 x2 x3 =
  trans
    (cong (quarter *_)
      (sumRationalCong (allCyclicIndices four) _ _
        (λ coordinate →
          average012Explicit field x0 x1 x2 coordinate)))
    (trans
      (cong (quarter *_)
        (sumRationalScale quarter3 (allCyclicIndices four)
          (sum210 field)))
      (ℚRing.solve-∀))

------------------------------------------------------------------------
-- Reverse the four finite sums by six adjacent Fubini swaps.
------------------------------------------------------------------------

reverseSiteSumEqualsCoordinateSum : ∀ field →
  reverseSiteSum field
  ≡ sumRational (allCyclicIndices four) (λ x0 →
      sumRational (allCyclicIndices four) (λ x1 →
        sumRational (allCyclicIndices four) (λ x2 →
          sumRational (allCyclicIndices four) (λ x3 →
            field (pair (pair x0 x1) (pair x2 x3))))))
reverseSiteSumEqualsCoordinateSum field =
  trans
    (sumRationalCong (allCyclicIndices four) _ _ (λ x3 →
      sumRationalCong (allCyclicIndices four) _ _ (λ x2 →
        sumSwap (allCyclicIndices four) (allCyclicIndices four)
          (λ x1 x0 → field (pair (pair x0 x1) (pair x2 x3))))))
    (trans
      (sumRationalCong (allCyclicIndices four) _ _ (λ x3 →
        sumSwap (allCyclicIndices four) (allCyclicIndices four)
          (λ x2 x0 →
            sumRational (allCyclicIndices four) (λ x1 →
              field (pair (pair x0 x1) (pair x2 x3))))))
      (trans
        (sumSwap (allCyclicIndices four) (allCyclicIndices four)
          (λ x3 x0 →
            sumRational (allCyclicIndices four) (λ x2 →
              sumRational (allCyclicIndices four) (λ x1 →
                field (pair (pair x0 x1) (pair x2 x3))))))
        (trans
          (sumRationalCong (allCyclicIndices four) _ _ (λ x0 →
            sumSwap (allCyclicIndices four) (allCyclicIndices four)
              (λ x3 x2 →
                sumRational (allCyclicIndices four) (λ x1 →
                  field (pair (pair x0 x1) (pair x2 x3))))))
          (trans
            (sumRationalCong (allCyclicIndices four) _ _ (λ x0 →
              sumRationalCong (allCyclicIndices four) _ _ (λ x2 →
                sumSwap (allCyclicIndices four) (allCyclicIndices four)
                  (λ x3 x1 →
                    field (pair (pair x0 x1) (pair x2 x3))))))
            (sumRationalCong (allCyclicIndices four) _ _ (λ x0 →
              sumSwap (allCyclicIndices four) (allCyclicIndices four)
                (λ x2 x1 →
                  sumRational (allCyclicIndices four) (λ x3 →
                    field (pair (pair x0 x1) (pair x2 x3))))))))))

reverseSiteSumEqualsSiteSum : ∀ field →
  reverseSiteSum field ≡ siteSum4 field
reverseSiteSumEqualsSiteSum field =
  trans (reverseSiteSumEqualsCoordinateSum field) (sym (siteSumAsCoordinates field))

quarter4IsOneTwoFiftySix : quarter4 ≡ oneTwoFiftySix
quarter4IsOneTwoFiftySix = ℚRing.solve-∀

average0123EqualsGlobalMean : ∀ field site →
  average0123 field site ≡ oneTwoFiftySix * siteSum4 field
average0123EqualsGlobalMean field (pair (pair x0 x1) (pair x2 x3)) =
  trans
    (average0123Explicit field x0 x1 x2 x3)
    (trans
      (cong (quarter4 *_) (reverseSiteSumEqualsSiteSum field))
      (cong (λ coefficient → coefficient * siteSum4 field)
        quarter4IsOneTwoFiftySix))

fourAxisAverageGlobalMeanLevel : ProofLevel
fourAxisAverageGlobalMeanLevel = machineChecked
