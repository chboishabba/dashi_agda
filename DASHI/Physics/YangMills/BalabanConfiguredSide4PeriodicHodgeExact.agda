module DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact

two : ℚ
two = 1ℚ + 1ℚ

forwardDerivativeEnergy : Axis4 → SiteField side4 → ℚ
forwardDerivativeEnergy derivative fld =
  siteSum4 (λ site → sq (forwardDifference4 derivative fld site))

backwardDerivativeEnergy : Axis4 → SiteField side4 → ℚ
backwardDerivativeEnergy derivative fld =
  siteSum4 (λ site → sq (backwardDifference4 derivative fld site))

mixedForwardEnergy : Axis4 → Axis4 → SiteField side4 → SiteField side4 → ℚ
mixedForwardEnergy first second hFirst hSecond =
  siteSum4 (λ site →
    forwardDifference4 first hSecond site
    * forwardDifference4 second hFirst site)

mixedBackwardEnergy : Axis4 → Axis4 → SiteField side4 → SiteField side4 → ℚ
mixedBackwardEnergy first second hFirst hSecond =
  siteSum4 (λ site →
    backwardDifference4 first hFirst site
    * backwardDifference4 second hSecond site)

curlPlaneEnergy : PositivePlaquettePlane4 → ScalarBondField4 → ℚ
curlPlaneEnergy plane fld =
  siteSum4 (λ site → sq
    (forwardDifference4 (positivePlaneFirst plane)
      (fld (positivePlaneSecond plane)) site
    - forwardDifference4 (positivePlaneSecond plane)
      (fld (positivePlaneFirst plane)) site))

componentCurlEnergy : ScalarBondField4 → ℚ
componentCurlEnergy fld =
  sumRational positivePlaquettePlanes4 (λ plane → curlPlaneEnergy plane fld)

componentDivergenceEnergy : ScalarBondField4 → ℚ
componentDivergenceEnergy fld =
  siteSum4 (λ site → sq (literalPeriodicDivergenceScalar fld site))

componentPeriodicDifferenceEnergy : ScalarBondField4 → ℚ
componentPeriodicDifferenceEnergy fld =
  sumRational (allCyclicIndices four) (λ componentAxis →
    sumRational (allCyclicIndices four) (λ derivativeAxis →
      forwardDerivativeEnergy derivativeAxis (fld componentAxis)))

backwardDifferenceAsForwardAtBackward : ∀ axis fld site →
  backwardDifference4 axis fld site
  ≡ forwardDifference4 axis fld (shiftBackward4 axis site)
backwardDifferenceAsForwardAtBackward axis fld site =
  cong (λ s → fld s - fld (shiftBackward4 axis site))
    (sym (forwardAfterBackward4 axis site))

forwardBackwardNormSqExact : ∀ axis fld →
  backwardDerivativeEnergy axis fld ≡ forwardDerivativeEnergy axis fld
forwardBackwardNormSqExact axis fld =
  trans
    (siteSum4Cong
      (λ site → sq (backwardDifference4 axis fld site))
      (λ site → sq (forwardDifference4 axis fld (shiftBackward4 axis site)))
      (λ site → cong sq (backwardDifferenceAsForwardAtBackward axis fld site)))
    (periodicBackwardReindexing axis
      (λ site → sq (forwardDifference4 axis fld site)))

siteSum4ThreeTerms : ∀ first second third →
  siteSum4 (λ site → first site + (second site + third site))
  ≡ siteSum4 first + (siteSum4 second + siteSum4 third)
siteSum4ThreeTerms first second third =
  trans
    (siteSum4Add first (λ site → second site + third site))
    (cong (siteSum4 first +_) (siteSum4Add second third))

sqSubExpandRaw : ∀ a b → (a - b) * (a - b) ≡ a * a + (b * b + (- two) * (a * b))
sqSubExpandRaw = ℚRing.solve-∀

negTwoScaleSubRaw : ∀ a b c → a + (b + (- two) * c) ≡ a + (b - two * c)
negTwoScaleSubRaw = ℚRing.solve-∀

positivePlaneSquareExpansion : ∀ plane fld →
  curlPlaneEnergy plane fld
  ≡ forwardDerivativeEnergy (positivePlaneFirst plane)
      (fld (positivePlaneSecond plane))
    + (forwardDerivativeEnergy (positivePlaneSecond plane)
        (fld (positivePlaneFirst plane))
    - two * mixedForwardEnergy
        (positivePlaneFirst plane) (positivePlaneSecond plane)
        (fld (positivePlaneFirst plane))
        (fld (positivePlaneSecond plane)))
positivePlaneSquareExpansion plane fld =
  let dFirst = forwardDifference4 (positivePlaneFirst plane) (fld (positivePlaneSecond plane))
      dSecond = forwardDifference4 (positivePlaneSecond plane) (fld (positivePlaneFirst plane))
  in
  trans
    (siteSum4Cong
      (λ site → sq (dFirst site - dSecond site))
      (λ site → sq (dFirst site) + (sq (dSecond site) + (- two) * (dFirst site * dSecond site)))
      (λ site → sqSubExpandRaw (dFirst site) (dSecond site)))
    (trans
      (siteSum4ThreeTerms
        (λ site → sq (dFirst site))
        (λ site → sq (dSecond site))
        (λ site → (- two) * (dFirst site * dSecond site)))
      (trans
        (cong (forwardDerivativeEnergy (positivePlaneFirst plane) (fld (positivePlaneSecond plane)) +_)
          (cong (forwardDerivativeEnergy (positivePlaneSecond plane) (fld (positivePlaneFirst plane)) +_)
            (siteSum4Scale (- two) (λ site → dFirst site * dSecond site))))
        (negTwoScaleSubRaw
          (forwardDerivativeEnergy (positivePlaneFirst plane) (fld (positivePlaneSecond plane)))
          (forwardDerivativeEnergy (positivePlaneSecond plane) (fld (positivePlaneFirst plane)))
          (mixedForwardEnergy (positivePlaneFirst plane) (positivePlaneSecond plane)
            (fld (positivePlaneFirst plane)) (fld (positivePlaneSecond plane))))))

componentCurlExpanded : ScalarBondField4 → ℚ
componentCurlExpanded fld =
  (forwardDerivativeEnergy axis0 (fld axis1)
    + forwardDerivativeEnergy axis1 (fld axis0)
    - two * mixedForwardEnergy axis0 axis1 (fld axis0) (fld axis1))
  + ((forwardDerivativeEnergy axis0 (fld axis2)
    + forwardDerivativeEnergy axis2 (fld axis0)
    - two * mixedForwardEnergy axis0 axis2 (fld axis0) (fld axis2))
  + ((forwardDerivativeEnergy axis0 (fld axis3)
    + forwardDerivativeEnergy axis3 (fld axis0)
    - two * mixedForwardEnergy axis0 axis3 (fld axis0) (fld axis3))
  + ((forwardDerivativeEnergy axis1 (fld axis2)
    + forwardDerivativeEnergy axis2 (fld axis1)
    - two * mixedForwardEnergy axis1 axis2 (fld axis1) (fld axis2))
  + ((forwardDerivativeEnergy axis1 (fld axis3)
    + forwardDerivativeEnergy axis3 (fld axis1)
    - two * mixedForwardEnergy axis1 axis3 (fld axis1) (fld axis3))
  + (forwardDerivativeEnergy axis2 (fld axis3)
    + forwardDerivativeEnergy axis3 (fld axis2)
    - two * mixedForwardEnergy axis2 axis3 (fld axis2) (fld axis3))))))

curlSixPlanesRaw :
  ∀ a01 b01 m01 a02 b02 m02 a03 b03 m03 a12 b12 m12 a13 b13 m13 a23 b23 m23 →
  (a01 + (b01 - m01)) + ((a02 + (b02 - m02)) + ((a03 + (b03 - m03)) +
  ((a12 + (b12 - m12)) + ((a13 + (b13 - m13)) + ((a23 + (b23 - m23)) + 0ℚ)))))
  ≡ (a01 + b01 - m01) + ((a02 + b02 - m02) + ((a03 + b03 - m03) +
    ((a12 + b12 - m12) + ((a13 + b13 - m13) + (a23 + b23 - m23)))))
curlSixPlanesRaw = ℚRing.solve-∀

componentCurlEnergyExpansion : ∀ fld →
  componentCurlEnergy fld ≡ componentCurlExpanded fld
componentCurlEnergyExpansion fld =
  trans
    (cong₂ _+_ (positivePlaneSquareExpansion plane01 fld)
      (cong₂ _+_ (positivePlaneSquareExpansion plane02 fld)
        (cong₂ _+_ (positivePlaneSquareExpansion plane03 fld)
          (cong₂ _+_ (positivePlaneSquareExpansion plane12 fld)
            (cong₂ _+_ (positivePlaneSquareExpansion plane13 fld)
              (cong (_+ 0ℚ) (positivePlaneSquareExpansion plane23 fld)))))))
    (curlSixPlanesRaw
      (forwardDerivativeEnergy axis0 (fld axis1))
      (forwardDerivativeEnergy axis1 (fld axis0))
      (two * mixedForwardEnergy axis0 axis1 (fld axis0) (fld axis1))
      (forwardDerivativeEnergy axis0 (fld axis2))
      (forwardDerivativeEnergy axis2 (fld axis0))
      (two * mixedForwardEnergy axis0 axis2 (fld axis0) (fld axis2))
      (forwardDerivativeEnergy axis0 (fld axis3))
      (forwardDerivativeEnergy axis3 (fld axis0))
      (two * mixedForwardEnergy axis0 axis3 (fld axis0) (fld axis3))
      (forwardDerivativeEnergy axis1 (fld axis2))
      (forwardDerivativeEnergy axis2 (fld axis1))
      (two * mixedForwardEnergy axis1 axis2 (fld axis1) (fld axis2))
      (forwardDerivativeEnergy axis1 (fld axis3))
      (forwardDerivativeEnergy axis3 (fld axis1))
      (two * mixedForwardEnergy axis1 axis3 (fld axis1) (fld axis3))
      (forwardDerivativeEnergy axis2 (fld axis3))
      (forwardDerivativeEnergy axis3 (fld axis2))
      (two * mixedForwardEnergy axis2 axis3 (fld axis2) (fld axis3)))

siteSum4TenTerms : ∀ t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 →
  siteSum4 (λ site →
    t0 site + (t1 site + (t2 site + (t3 site +
    (t4 site + (t5 site + (t6 site + (t7 site + (t8 site + t9 site)))))))))
  ≡ siteSum4 t0 + (siteSum4 t1 + (siteSum4 t2 + (siteSum4 t3 +
    (siteSum4 t4 + (siteSum4 t5 + (siteSum4 t6 +
    (siteSum4 t7 + (siteSum4 t8 + siteSum4 t9))))))))
siteSum4TenTerms t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 =
  trans
    (siteSum4Add t0 (λ site → t1 site + (t2 site + (t3 site + (t4 site + (t5 site + (t6 site + (t7 site + (t8 site + t9 site)))))))))
    (cong (siteSum4 t0 +_)
      (trans
        (siteSum4Add t1 (λ site → t2 site + (t3 site + (t4 site + (t5 site + (t6 site + (t7 site + (t8 site + t9 site))))))))
        (cong (siteSum4 t1 +_)
          (trans
            (siteSum4Add t2 (λ site → t3 site + (t4 site + (t5 site + (t6 site + (t7 site + (t8 site + t9 site)))))))
            (cong (siteSum4 t2 +_)
              (trans
                (siteSum4Add t3 (λ site → t4 site + (t5 site + (t6 site + (t7 site + (t8 site + t9 site))))))
                (cong (siteSum4 t3 +_)
                  (trans
                    (siteSum4Add t4 (λ site → t5 site + (t6 site + (t7 site + (t8 site + t9 site)))))
                    (cong (siteSum4 t4 +_)
                      (trans
                        (siteSum4Add t5 (λ site → t6 site + (t7 site + (t8 site + t9 site))))
                        (cong (siteSum4 t5 +_)
                          (trans
                            (siteSum4Add t6 (λ site → t7 site + (t8 site + t9 site)))
                            (cong (siteSum4 t6 +_)
                              (trans
                                (siteSum4Add t7 (λ site → t8 site + t9 site))
                                (cong (siteSum4 t7 +_)
                                  (siteSum4Add t8 t9))))))))))))))))

componentDivergenceExpanded : ScalarBondField4 → ℚ
componentDivergenceExpanded fld =
  backwardDerivativeEnergy axis0 (fld axis0)
  + (backwardDerivativeEnergy axis1 (fld axis1)
  + (backwardDerivativeEnergy axis2 (fld axis2)
  + (backwardDerivativeEnergy axis3 (fld axis3)
  + (two * mixedBackwardEnergy axis0 axis1 (fld axis0) (fld axis1)
  + (two * mixedBackwardEnergy axis0 axis2 (fld axis0) (fld axis2)
  + (two * mixedBackwardEnergy axis0 axis3 (fld axis0) (fld axis3)
  + (two * mixedBackwardEnergy axis1 axis2 (fld axis1) (fld axis2)
  + (two * mixedBackwardEnergy axis1 axis3 (fld axis1) (fld axis3)
  + two * mixedBackwardEnergy axis2 axis3 (fld axis2) (fld axis3)))))))))

divFourSquareExpandRaw : ∀ d0 d1 d2 d3 →
  (d0 + (d1 + (d2 + (d3 + 0ℚ)))) * (d0 + (d1 + (d2 + (d3 + 0ℚ))))
  ≡ d0 * d0 + (d1 * d1 + (d2 * d2 + (d3 * d3 +
    (two * (d0 * d1) + (two * (d0 * d2) + (two * (d0 * d3) +
    (two * (d1 * d2) + (two * (d1 * d3) + two * (d2 * d3)))))))))
divFourSquareExpandRaw = ℚRing.solve-∀

componentDivergenceEnergyExpansion : ∀ fld →
  componentDivergenceEnergy fld ≡ componentDivergenceExpanded fld
componentDivergenceEnergyExpansion fld =
  let d0 = backwardDifference4 axis0 (fld axis0)
      d1 = backwardDifference4 axis1 (fld axis1)
      d2 = backwardDifference4 axis2 (fld axis2)
      d3 = backwardDifference4 axis3 (fld axis3)
      t0 = λ site → sq (d0 site)
      t1 = λ site → sq (d1 site)
      t2 = λ site → sq (d2 site)
      t3 = λ site → sq (d3 site)
      t4 = λ site → two * (d0 site * d1 site)
      t5 = λ site → two * (d0 site * d2 site)
      t6 = λ site → two * (d0 site * d3 site)
      t7 = λ site → two * (d1 site * d2 site)
      t8 = λ site → two * (d1 site * d3 site)
      t9 = λ site → two * (d2 site * d3 site)
  in
  trans
    (siteSum4Cong
      (λ site → sq (literalPeriodicDivergenceScalar fld site))
      (λ site → t0 site + (t1 site + (t2 site + (t3 site +
        (t4 site + (t5 site + (t6 site + (t7 site + (t8 site + t9 site)))))))))
      (λ site → divFourSquareExpandRaw (d0 site) (d1 site) (d2 site) (d3 site)))
    (trans
      (siteSum4TenTerms t0 t1 t2 t3 t4 t5 t6 t7 t8 t9)
      (cong (backwardDerivativeEnergy axis0 (fld axis0) +_)
        (cong (backwardDerivativeEnergy axis1 (fld axis1) +_)
          (cong (backwardDerivativeEnergy axis2 (fld axis2) +_)
            (cong (backwardDerivativeEnergy axis3 (fld axis3) +_)
              (cong₂ _+_ (siteSum4Scale two (λ site → d0 site * d1 site))
                (cong₂ _+_ (siteSum4Scale two (λ site → d0 site * d2 site))
                  (cong₂ _+_ (siteSum4Scale two (λ site → d0 site * d3 site))
                    (cong₂ _+_ (siteSum4Scale two (λ site → d1 site * d2 site))
                      (cong₂ _+_ (siteSum4Scale two (λ site → d1 site * d3 site))
                        (siteSum4Scale two (λ site → d2 site * d3 site))))))))))))

componentPeriodicDifferenceExpanded : ScalarBondField4 → ℚ
componentPeriodicDifferenceExpanded fld =
  forwardDerivativeEnergy axis0 (fld axis0)
  + (forwardDerivativeEnergy axis1 (fld axis0)
  + (forwardDerivativeEnergy axis2 (fld axis0)
  + (forwardDerivativeEnergy axis3 (fld axis0)
  + (forwardDerivativeEnergy axis0 (fld axis1)
  + (forwardDerivativeEnergy axis1 (fld axis1)
  + (forwardDerivativeEnergy axis2 (fld axis1)
  + (forwardDerivativeEnergy axis3 (fld axis1)
  + (forwardDerivativeEnergy axis0 (fld axis2)
  + (forwardDerivativeEnergy axis1 (fld axis2)
  + (forwardDerivativeEnergy axis2 (fld axis2)
  + (forwardDerivativeEnergy axis3 (fld axis2)
  + (forwardDerivativeEnergy axis0 (fld axis3)
  + (forwardDerivativeEnergy axis1 (fld axis3)
  + (forwardDerivativeEnergy axis2 (fld axis3)
  + forwardDerivativeEnergy axis3 (fld axis3)))))))))))))))

diffSixteenExpandRaw :
  ∀ e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33 →
  (e00 + (e10 + (e20 + (e30 + 0ℚ)))) +
  ((e01 + (e11 + (e21 + (e31 + 0ℚ)))) +
  ((e02 + (e12 + (e22 + (e32 + 0ℚ)))) +
  ((e03 + (e13 + (e23 + (e33 + 0ℚ)))) + 0ℚ)))
  ≡ e00 + (e10 + (e20 + (e30 + (e01 + (e11 + (e21 + (e31 +
    (e02 + (e12 + (e22 + (e32 + (e03 + (e13 + (e23 + e33))))))))))))))
diffSixteenExpandRaw = ℚRing.solve-∀

componentPeriodicDifferenceEnergyExpansion : ∀ fld →
  componentPeriodicDifferenceEnergy fld
  ≡ componentPeriodicDifferenceExpanded fld
componentPeriodicDifferenceEnergyExpansion fld =
  diffSixteenExpandRaw
    (forwardDerivativeEnergy axis0 (fld axis0))
    (forwardDerivativeEnergy axis1 (fld axis0))
    (forwardDerivativeEnergy axis2 (fld axis0))
    (forwardDerivativeEnergy axis3 (fld axis0))
    (forwardDerivativeEnergy axis0 (fld axis1))
    (forwardDerivativeEnergy axis1 (fld axis1))
    (forwardDerivativeEnergy axis2 (fld axis1))
    (forwardDerivativeEnergy axis3 (fld axis1))
    (forwardDerivativeEnergy axis0 (fld axis2))
    (forwardDerivativeEnergy axis1 (fld axis2))
    (forwardDerivativeEnergy axis2 (fld axis2))
    (forwardDerivativeEnergy axis3 (fld axis2))
    (forwardDerivativeEnergy axis0 (fld axis3))
    (forwardDerivativeEnergy axis1 (fld axis3))
    (forwardDerivativeEnergy axis2 (fld axis3))
    (forwardDerivativeEnergy axis3 (fld axis3))

hodgePartitionAlgebraRaw :
  ∀ e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33
    m01 m02 m03 m12 m13 m23 →
  ((e01 + e10 - two * m01) + ((e02 + e20 - two * m02) + ((e03 + e30 - two * m03) +
  ((e12 + e21 - two * m12) + ((e13 + e31 - two * m13) + (e23 + e32 - two * m23))))))
  + (e00 + (e11 + (e22 + (e33 + (two * m01 + (two * m02 + (two * m03 +
    (two * m12 + (two * m13 + two * m23)))))))))
  ≡ e00 + (e10 + (e20 + (e30 + (e01 + (e11 + (e21 + (e31 +
    (e02 + (e12 + (e22 + (e32 + (e03 + (e13 + (e23 + e33))))))))))))))
hodgePartitionAlgebraRaw = ℚRing.solve-∀

fourAxisDiagonalOffDiagonalPartition : ∀ fld →
  componentCurlExpanded fld + componentDivergenceExpanded fld
  ≡ componentPeriodicDifferenceExpanded fld
fourAxisDiagonalOffDiagonalPartition fld =
  let e00 = forwardDerivativeEnergy axis0 (fld axis0)
      e10 = forwardDerivativeEnergy axis1 (fld axis0)
      e20 = forwardDerivativeEnergy axis2 (fld axis0)
      e30 = forwardDerivativeEnergy axis3 (fld axis0)
      e01 = forwardDerivativeEnergy axis0 (fld axis1)
      e11 = forwardDerivativeEnergy axis1 (fld axis1)
      e21 = forwardDerivativeEnergy axis2 (fld axis1)
      e31 = forwardDerivativeEnergy axis3 (fld axis1)
      e02 = forwardDerivativeEnergy axis0 (fld axis2)
      e12 = forwardDerivativeEnergy axis1 (fld axis2)
      e22 = forwardDerivativeEnergy axis2 (fld axis2)
      e32 = forwardDerivativeEnergy axis3 (fld axis2)
      e03 = forwardDerivativeEnergy axis0 (fld axis3)
      e13 = forwardDerivativeEnergy axis1 (fld axis3)
      e23 = forwardDerivativeEnergy axis2 (fld axis3)
      e33 = forwardDerivativeEnergy axis3 (fld axis3)
      m01 = mixedBackwardEnergy axis0 axis1 (fld axis0) (fld axis1)
      m02 = mixedBackwardEnergy axis0 axis2 (fld axis0) (fld axis2)
      m03 = mixedBackwardEnergy axis0 axis3 (fld axis0) (fld axis3)
      m12 = mixedBackwardEnergy axis1 axis2 (fld axis1) (fld axis2)
      m13 = mixedBackwardEnergy axis1 axis3 (fld axis1) (fld axis3)
      m23 = mixedBackwardEnergy axis2 axis3 (fld axis2) (fld axis3)
      curlConvert :
        componentCurlExpanded fld
        ≡ (e01 + e10 - two * m01) + ((e02 + e20 - two * m02) + ((e03 + e30 - two * m03) +
          ((e12 + e21 - two * m12) + ((e13 + e31 - two * m13) + (e23 + e32 - two * m23)))))
      curlConvert =
        cong₂ _+_ (cong (λ m → e01 + e10 - two * m) (curlCrossTermEqualsDivergenceCrossTerm axis0 axis1 (fld axis0) (fld axis1)))
          (cong₂ _+_ (cong (λ m → e02 + e20 - two * m) (curlCrossTermEqualsDivergenceCrossTerm axis0 axis2 (fld axis0) (fld axis2)))
            (cong₂ _+_ (cong (λ m → e03 + e30 - two * m) (curlCrossTermEqualsDivergenceCrossTerm axis0 axis3 (fld axis0) (fld axis3)))
              (cong₂ _+_ (cong (λ m → e12 + e21 - two * m) (curlCrossTermEqualsDivergenceCrossTerm axis1 axis2 (fld axis1) (fld axis2)))
                (cong₂ _+_ (cong (λ m → e13 + e31 - two * m) (curlCrossTermEqualsDivergenceCrossTerm axis1 axis3 (fld axis1) (fld axis3)))
                  (cong (λ m → e23 + e32 - two * m) (curlCrossTermEqualsDivergenceCrossTerm axis2 axis3 (fld axis2) (fld axis3)))))))
      divConvert :
        componentDivergenceExpanded fld
        ≡ e00 + (e11 + (e22 + (e33 + (two * m01 + (two * m02 + (two * m03 +
          (two * m12 + (two * m13 + two * m23))))))))
      divConvert =
        cong₂ _+_ (forwardBackwardNormSqExact axis0 (fld axis0))
          (cong₂ _+_ (forwardBackwardNormSqExact axis1 (fld axis1))
            (cong₂ _+_ (forwardBackwardNormSqExact axis2 (fld axis2))
              (cong (_+ (two * m01 + (two * m02 + (two * m03 + (two * m12 + (two * m13 + two * m23))))))
                (forwardBackwardNormSqExact axis3 (fld axis3)))))
  in
  trans
    (cong₂ _+_ curlConvert divConvert)
    (hodgePartitionAlgebraRaw
      e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33
      m01 m02 m03 m12 m13 m23)

componentDiscreteCurlDivergenceHodgeIdentity : ∀ fld →
  componentCurlEnergy fld + componentDivergenceEnergy fld
  ≡ componentPeriodicDifferenceEnergy fld
componentDiscreteCurlDivergenceHodgeIdentity fld =
  trans
    (cong₂ _+_
      (componentCurlEnergyExpansion fld)
      (componentDivergenceEnergyExpansion fld))
    (trans
      (fourAxisDiagonalOffDiagonalPartition fld)
      (sym (componentPeriodicDifferenceEnergyExpansion fld)))

configuredSide4PeriodicHodgeIdentityLevel : ProofLevel
configuredSide4PeriodicHodgeIdentityLevel = machineChecked
