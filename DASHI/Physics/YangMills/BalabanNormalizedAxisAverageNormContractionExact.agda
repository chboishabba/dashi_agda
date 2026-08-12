module DASHI.Physics.YangMills.BalabanNormalizedAxisAverageNormContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
--
-- For the repository's literal L^4 carrier, prove that every normalized
-- coordinate average is an orthogonal projection and hence contracts the
-- global finite L2 norm.  Unlike the older side-four theorem, this proof is
-- parameterized by an arbitrary finite side L and by the exact normalization
-- witness carried by NormalizedAxisAverageData.  It is therefore directly
-- consumable by the source-admissible L=13 Gate-I migration.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; squareNonnegative; baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
import DASHI.Physics.YangMills.BalabanNormalizedAxisAverageExact as Average

FieldEqual : ∀ {L} → SiteField L → SiteField L → Set
FieldEqual left right = ∀ site → left site ≡ right site

addField : ∀ {L} → SiteField L → SiteField L → SiteField L
addField left right site = left site + right site

subtractField : ∀ {L} → SiteField L → SiteField L → SiteField L
subtractField left right site = left site - right site

axisResidual :
  ∀ {L} → Average.NormalizedAxisAverageData L →
  SiteField L → Axis4 → SiteField L
axisResidual dataSet siteField axis =
  subtractField siteField (Average.axisAverage dataSet siteField axis)

sumRationalNonnegative :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  (∀ value → 0ℚ ≤ term value) →
  0ℚ ≤ sumRational values term
sumRationalNonnegative [] term pointwise = ℚP.≤-refl
sumRationalNonnegative (value ∷ values) term pointwise =
  subst
    (λ left → left ≤ term value + sumRational values term)
    (ℚP.+-identityˡ 0ℚ)
    (ℚP.+-mono-≤
      (pointwise value)
      (sumRationalNonnegative values term pointwise))

globalNormSq : ∀ {L} → SiteField L → ℚ
globalNormSq field = globalBlockInner field field

globalNormSqNonnegative : ∀ {L} (field : SiteField L) →
  0ℚ ≤ globalNormSq field
globalNormSqNonnegative {L} field =
  sumRationalNonnegative
    (physicalBlockSites L)
    (λ site → sq (field site))
    (λ site → squareNonnegative (field site))

globalNormRespectsPointwise :
  ∀ {L} {left right : SiteField L} →
  FieldEqual left right → globalNormSq left ≡ globalNormSq right
globalNormRespectsPointwise {L} {left} {right} equality =
  sumRationalCong
    (physicalBlockSites L)
    (λ site → left site * left site)
    (λ site → right site * right site)
    (λ site → cong₂ _*_ (equality site) (equality site))

sumRationalSubtractLocal :
  ∀ {A : Set} (values : List A) (f g : A → ℚ) →
  sumRational values (λ value → f value - g value)
  ≡ sumRational values f - sumRational values g
sumRationalSubtractLocal [] f g = ℚRing.solve-∀
sumRationalSubtractLocal (value ∷ values) f g
  rewrite sumRationalSubtractLocal values f g = ℚRing.solve-∀

innerSubtractLeft :
  ∀ {L} (left right test : SiteField L) →
  globalBlockInner (subtractField left right) test
  ≡ globalBlockInner left test - globalBlockInner right test
innerSubtractLeft {L} left right test =
  trans
    (sumRationalCong
      (physicalBlockSites L)
      (λ site → (left site - right site) * test site)
      (λ site → left site * test site - right site * test site)
      (λ site → ℚRing.solve-∀))
    (sumRationalSubtractLocal
      (physicalBlockSites L)
      (λ site → left site * test site)
      (λ site → right site * test site))

innerRespectsRightPointwise :
  ∀ {L} (left : SiteField L) {right right′ : SiteField L} →
  FieldEqual right right′ →
  globalBlockInner left right ≡ globalBlockInner left right′
innerRespectsRightPointwise {L} left {right} {right′} equality =
  sumRationalCong
    (physicalBlockSites L)
    (λ site → left site * right site)
    (λ site → left site * right′ site)
    (λ site → cong (λ value → left site * value) (equality site))

axisAverageFixedPointwise :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    axis field →
  FieldEqual
    (Average.axisAverage dataSet
      (Average.axisAverage dataSet field axis) axis)
    (Average.axisAverage dataSet field axis)
axisAverageFixedPointwise dataSet axis field site =
  Average.axisAverageIdempotent dataSet field axis site

residualOrthogonalToAverage :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    field axis →
  globalBlockInner
    (axisResidual dataSet field axis)
    (Average.axisAverage dataSet field axis)
  ≡ 0ℚ
residualOrthogonalToAverage dataSet field axis =
  trans
    (innerSubtractLeft
      field (Average.axisAverage dataSet field axis)
      (Average.axisAverage dataSet field axis))
    (trans
      (cong
        (λ value →
          globalBlockInner field (Average.axisAverage dataSet field axis)
          - value)
        (Average.axisAverageSelfAdjoint dataSet axis field
          (Average.axisAverage dataSet field axis)))
      (trans
        (cong
          (λ value →
            globalBlockInner field (Average.axisAverage dataSet field axis)
            - value)
          (innerRespectsRightPointwise field
            (axisAverageFixedPointwise dataSet axis field)))
        (ℚRing.solve-∀)))

twoFieldSquareExpansion :
  ∀ {L} (left right : SiteField L) →
  globalNormSq (addField left right)
  ≡ globalNormSq left + globalNormSq right
    + (1ℚ + 1ℚ) * globalBlockInner left right
twoFieldSquareExpansion {L} left right =
  trans
    (sumRationalCong
      (physicalBlockSites L)
      (λ site → sq (left site + right site))
      (λ site →
        sq (left site) + sq (right site)
        + (1ℚ + 1ℚ) * (left site * right site))
      (λ site → ℚRing.solve-∀))
    (trans
      (sumRationalAdd
        (physicalBlockSites L)
        (λ site → sq (left site))
        (λ site → sq (right site)
          + (1ℚ + 1ℚ) * (left site * right site)))
      (trans
        (cong₂ _+_ refl
          (sumRationalAdd
            (physicalBlockSites L)
            (λ site → sq (right site))
            (λ site → (1ℚ + 1ℚ) * (left site * right site))))
        (trans
          (cong₂ _+_ refl
            (cong₂ _+_ refl
              (sumRationalScale
                (1ℚ + 1ℚ)
                (physicalBlockSites L)
                (λ site → left site * right site))))
          (ℚRing.solve-∀
            (globalNormSq left)
            (globalNormSq right)
            (globalBlockInner left right)))))

residualPlusAveragePointwise :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    field axis →
  FieldEqual
    (addField
      (axisResidual dataSet field axis)
      (Average.axisAverage dataSet field axis))
    field
residualPlusAveragePointwise dataSet field axis site = ℚRing.solve-∀

axisAveragePythagoras :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    field axis →
  globalNormSq field
  ≡ globalNormSq (axisResidual dataSet field axis)
    + globalNormSq (Average.axisAverage dataSet field axis)
axisAveragePythagoras dataSet field axis =
  trans
    (sym (globalNormRespectsPointwise
      (residualPlusAveragePointwise dataSet field axis)))
    (trans
      (twoFieldSquareExpansion
        (axisResidual dataSet field axis)
        (Average.axisAverage dataSet field axis))
      (trans
        (cong
          (λ cross →
            globalNormSq (axisResidual dataSet field axis)
            + globalNormSq (Average.axisAverage dataSet field axis)
            + (1ℚ + 1ℚ) * cross)
          (residualOrthogonalToAverage dataSet field axis))
        (ℚRing.solve-∀)))

axisAverageNormContraction :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    field axis →
  globalNormSq (Average.axisAverage dataSet field axis)
  ≤ globalNormSq field
axisAverageNormContraction dataSet field axis =
  let
    pythagorasAverageFirst :
      globalNormSq field
      ≡ globalNormSq (Average.axisAverage dataSet field axis)
        + globalNormSq (axisResidual dataSet field axis)
    pythagorasAverageFirst =
      trans (axisAveragePythagoras dataSet field axis) (ℚRing.solve-∀)
  in
  subst
    (λ upper →
      globalNormSq (Average.axisAverage dataSet field axis) ≤ upper)
    (sym pythagorasAverageFirst)
    (baseBelowBasePlusRemainder
      (globalNormSq (Average.axisAverage dataSet field axis))
      (globalNormSq (axisResidual dataSet field axis))
      (globalNormSqNonnegative (axisResidual dataSet field axis)))

normalizedAxisAveragePythagorasLevel : ProofLevel
normalizedAxisAveragePythagorasLevel = machineChecked

normalizedAxisAverageNormContractionLevel : ProofLevel
normalizedAxisAverageNormContractionLevel = machineChecked
