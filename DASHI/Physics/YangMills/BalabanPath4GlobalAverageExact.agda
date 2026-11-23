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
sum0 fld x1 x2 x3 =
  sumRational (allCyclicIndices four) (λ x0 →
    fld (pair (pair x0 x1) (pair x2 x3)))

sum10 : SiteField side4 → CyclicIndex four → CyclicIndex four → ℚ
sum10 fld x2 x3 =
  sumRational (allCyclicIndices four) (λ x1 → sum0 fld x1 x2 x3)

sum210 : SiteField side4 → CyclicIndex four → ℚ
sum210 fld x3 =
  sumRational (allCyclicIndices four) (λ x2 → sum10 fld x2 x3)

reverseSiteSum : SiteField side4 → ℚ
reverseSiteSum fld =
  sumRational (allCyclicIndices four) (sum210 fld)

mulAssocRaw : ∀ a b c → a * (b * c) ≡ (a * b) * c
mulAssocRaw = ℚRing.solve-∀

average0Explicit : (fld : SiteField side4) (x0 x1 x2 x3 : CyclicIndex four) →
  average0 fld (pair (pair x0 x1) (pair x2 x3))
  ≡ quarter * sum0 fld x1 x2 x3
average0Explicit fld x0 x1 x2 x3 = refl

average01Explicit : (fld : SiteField side4) (x0 x1 x2 x3 : CyclicIndex four) →
  average01 fld (pair (pair x0 x1) (pair x2 x3))
  ≡ quarter2 * sum10 fld x2 x3
average01Explicit fld x0 x1 x2 x3 =
  trans
    (cong (quarter *_)
      (sumRationalCong (allCyclicIndices four)
        (λ coordinate → average0 fld (pair (pair x0 coordinate) (pair x2 x3)))
        (λ coordinate → quarter * sum0 fld coordinate x2 x3)
        (λ coordinate →
          average0Explicit fld x0 coordinate x2 x3)))
    (trans
      (cong (quarter *_)
        (sumRationalScale quarter (allCyclicIndices four)
          (λ coordinate → sum0 fld coordinate x2 x3)))
      (mulAssocRaw quarter quarter (sum10 fld x2 x3)))

average012Explicit : (fld : SiteField side4) (x0 x1 x2 x3 : CyclicIndex four) →
  average012 fld (pair (pair x0 x1) (pair x2 x3))
  ≡ quarter3 * sum210 fld x3
average012Explicit fld x0 x1 x2 x3 =
  trans
    (cong (quarter *_)
      (sumRationalCong (allCyclicIndices four)
        (λ coordinate → average01 fld (pair (pair x0 x1) (pair coordinate x3)))
        (λ coordinate → quarter2 * sum10 fld coordinate x3)
        (λ coordinate →
          average01Explicit fld x0 x1 coordinate x3)))
    (trans
      (cong (quarter *_)
        (sumRationalScale quarter2 (allCyclicIndices four)
          (λ coordinate → sum10 fld coordinate x3)))
      (mulAssocRaw quarter quarter2 (sum210 fld x3)))

average0123Explicit : (fld : SiteField side4) (x0 x1 x2 x3 : CyclicIndex four) →
  average0123 fld (pair (pair x0 x1) (pair x2 x3))
  ≡ quarter4 * reverseSiteSum fld
average0123Explicit fld x0 x1 x2 x3 =
  trans
    (cong (quarter *_)
      (sumRationalCong (allCyclicIndices four)
        (λ coordinate → average012 fld (pair (pair x0 x1) (pair x2 coordinate)))
        (λ coordinate → quarter3 * sum210 fld coordinate)
        (λ coordinate →
          average012Explicit fld x0 x1 x2 coordinate)))
    (trans
      (cong (quarter *_)
        (sumRationalScale quarter3 (allCyclicIndices four)
          (sum210 fld)))
      (mulAssocRaw quarter quarter3 (reverseSiteSum fld)))

------------------------------------------------------------------------
-- Reverse the four finite sums by six adjacent Fubini swaps.
------------------------------------------------------------------------

reverseSiteSumEqualsCoordinateSum : (fld : SiteField side4) →
  reverseSiteSum fld
  ≡ sumRational (allCyclicIndices four) (λ x0 →
      sumRational (allCyclicIndices four) (λ x1 →
        sumRational (allCyclicIndices four) (λ x2 →
          sumRational (allCyclicIndices four) (λ x3 →
            fld (pair (pair x0 x1) (pair x2 x3))))))
reverseSiteSumEqualsCoordinateSum fld =
  trans
    (sumRationalCong (allCyclicIndices four)
      (sum210 fld)
      (λ x3 → sumRational (allCyclicIndices four) (λ x2 →
        sumRational (allCyclicIndices four) (λ x0 →
          sumRational (allCyclicIndices four) (λ x1 →
            fld (pair (pair x0 x1) (pair x2 x3))))))
      (λ x3 →
        sumRationalCong (allCyclicIndices four)
          (λ x2 → sum10 fld x2 x3)
          (λ x2 → sumRational (allCyclicIndices four) (λ x0 →
            sumRational (allCyclicIndices four) (λ x1 →
              fld (pair (pair x0 x1) (pair x2 x3)))))
          (λ x2 →
            sumSwap (allCyclicIndices four) (allCyclicIndices four)
              (λ x1 x0 → fld (pair (pair x0 x1) (pair x2 x3))))))
    (trans
      (sumRationalCong (allCyclicIndices four)
        (λ x3 → sumRational (allCyclicIndices four) (λ x2 →
          sumRational (allCyclicIndices four) (λ x0 →
            sumRational (allCyclicIndices four) (λ x1 →
              fld (pair (pair x0 x1) (pair x2 x3))))))
        (λ x3 → sumRational (allCyclicIndices four) (λ x0 →
          sumRational (allCyclicIndices four) (λ x2 →
            sumRational (allCyclicIndices four) (λ x1 →
              fld (pair (pair x0 x1) (pair x2 x3))))))
        (λ x3 →
          sumSwap (allCyclicIndices four) (allCyclicIndices four)
            (λ x2 x0 →
              sumRational (allCyclicIndices four) (λ x1 →
                fld (pair (pair x0 x1) (pair x2 x3))))))
      (trans
        (sumSwap (allCyclicIndices four) (allCyclicIndices four)
          (λ x3 x0 →
            sumRational (allCyclicIndices four) (λ x2 →
              sumRational (allCyclicIndices four) (λ x1 →
                fld (pair (pair x0 x1) (pair x2 x3))))))
        (trans
          (sumRationalCong (allCyclicIndices four)
            (λ x0 → sumRational (allCyclicIndices four) (λ x3 →
              sumRational (allCyclicIndices four) (λ x2 →
                sumRational (allCyclicIndices four) (λ x1 →
                  fld (pair (pair x0 x1) (pair x2 x3))))))
            (λ x0 → sumRational (allCyclicIndices four) (λ x2 →
              sumRational (allCyclicIndices four) (λ x3 →
                sumRational (allCyclicIndices four) (λ x1 →
                  fld (pair (pair x0 x1) (pair x2 x3))))))
            (λ x0 →
              sumSwap (allCyclicIndices four) (allCyclicIndices four)
                (λ x3 x2 →
                  sumRational (allCyclicIndices four) (λ x1 →
                    fld (pair (pair x0 x1) (pair x2 x3))))))
          (trans
            (sumRationalCong (allCyclicIndices four)
              (λ x0 → sumRational (allCyclicIndices four) (λ x2 →
                sumRational (allCyclicIndices four) (λ x3 →
                  sumRational (allCyclicIndices four) (λ x1 →
                    fld (pair (pair x0 x1) (pair x2 x3))))))
              (λ x0 → sumRational (allCyclicIndices four) (λ x2 →
                sumRational (allCyclicIndices four) (λ x1 →
                  sumRational (allCyclicIndices four) (λ x3 →
                    fld (pair (pair x0 x1) (pair x2 x3))))))
              (λ x0 →
                sumRationalCong (allCyclicIndices four)
                  (λ x2 → sumRational (allCyclicIndices four) (λ x3 →
                    sumRational (allCyclicIndices four) (λ x1 →
                      fld (pair (pair x0 x1) (pair x2 x3)))))
                  (λ x2 → sumRational (allCyclicIndices four) (λ x1 →
                    sumRational (allCyclicIndices four) (λ x3 →
                      fld (pair (pair x0 x1) (pair x2 x3)))))
                  (λ x2 →
                    sumSwap (allCyclicIndices four) (allCyclicIndices four)
                      (λ x3 x1 →
                        fld (pair (pair x0 x1) (pair x2 x3))))))
            (sumRationalCong (allCyclicIndices four)
              (λ x0 → sumRational (allCyclicIndices four) (λ x2 →
                sumRational (allCyclicIndices four) (λ x1 →
                  sumRational (allCyclicIndices four) (λ x3 →
                    fld (pair (pair x0 x1) (pair x2 x3))))))
              (λ x0 → sumRational (allCyclicIndices four) (λ x1 →
                sumRational (allCyclicIndices four) (λ x2 →
                  sumRational (allCyclicIndices four) (λ x3 →
                    fld (pair (pair x0 x1) (pair x2 x3))))))
              (λ x0 →
                sumSwap (allCyclicIndices four) (allCyclicIndices four)
                  (λ x2 x1 →
                    sumRational (allCyclicIndices four) (λ x3 →
                      fld (pair (pair x0 x1) (pair x2 x3))))))))))

reverseSiteSumEqualsSiteSum : (fld : SiteField side4) →
  reverseSiteSum fld ≡ siteSum4 fld
reverseSiteSumEqualsSiteSum fld =
  trans (reverseSiteSumEqualsCoordinateSum fld) (sym (siteSumAsCoordinates fld))

quarter4IsOneTwoFiftySix : quarter4 ≡ oneTwoFiftySix
quarter4IsOneTwoFiftySix = ℚRing.solve-∀

average0123EqualsGlobalMean : (fld : SiteField side4) (site : PhysicalBlockL side4) →
  average0123 fld site ≡ oneTwoFiftySix * siteSum4 fld
average0123EqualsGlobalMean fld (pair (pair x0 x1) (pair x2 x3)) =
  trans
    (average0123Explicit fld x0 x1 x2 x3)
    (trans
      (cong (quarter4 *_) (reverseSiteSumEqualsSiteSum fld))
      (cong (λ coefficient → coefficient * siteSum4 fld)
        quarter4IsOneTwoFiftySix))

fourAxisAverageGlobalMeanLevel : ProofLevel
fourAxisAverageGlobalMeanLevel = machineChecked
