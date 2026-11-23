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
--
-- OOM discipline:
--   * pointwise scalar identities may be solved locally;
--   * the global norm is registered once as a fibre observer;
--   * global closure algebra is discharged only through carrier-free scalar
--     lemmas, so reflection never reopens the physical L^4 representation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

import DASHI.Core.AtomicGlobalFibreLiftExact as FibreLift
import DASHI.Physics.YangMills.BalabanOpaqueGlobalAlgebraExact as OpaqueAlgebra

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; squareNonnegative; baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (Axis4)
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
globalNormSq fld = globalBlockInner fld fld

globalNormSqNonnegative : ∀ {L} (fld : SiteField L) →
  0ℚ ≤ globalNormSq fld
globalNormSqNonnegative {L} fld =
  sumRationalNonnegative
    (physicalBlockSites L)
    (λ site → sq (fld site))
    (λ site → squareNonnegative (fld site))

------------------------------------------------------------------------
-- The finite L2 norm is literally a fibre observer.  Its concrete physical
-- sum is opened exactly once here to prove pointwise-equality preservation.
------------------------------------------------------------------------

globalNormPreservesPointwise :
  ∀ {L} {left right : SiteField L} →
  FieldEqual left right → globalNormSq left ≡ globalNormSq right
globalNormPreservesPointwise {L} {left} {right} equality =
  sumRationalCong
    (physicalBlockSites L)
    (λ site → left site * left site)
    (λ site → right site * right site)
    (λ site → cong₂ _*_ (equality site) (equality site))

globalNormObserverLift :
  ∀ {L} → FibreLift.FibreObserverLift (globalNormSq {L})
globalNormObserverLift =
  FibreLift.fibre-observer-lift globalNormPreservesPointwise

globalNormRespectsPointwise :
  ∀ {L} {left right : SiteField L} →
  FieldEqual left right → globalNormSq left ≡ globalNormSq right
globalNormRespectsPointwise equality =
  FibreLift.atomicFamilyToGlobal globalNormObserverLift equality

diffMinus : ∀ a b c → (a - b) * c ≡ a * c - b * c
diffMinus = ℚRing.solve-∀

sqBinomialRaw : ∀ a b → (a + b) * (a + b) ≡ a * a + (b * b + (1ℚ + 1ℚ) * (a * b))
sqBinomialRaw = ℚRing.solve-∀

sqBinomial : ∀ a b → sq (a + b) ≡ sq a + (sq b + (1ℚ + 1ℚ) * (a * b))
sqBinomial a b = sqBinomialRaw a b

assocPlus3 : ∀ a b c → a + (b + c) ≡ (a + b) + c
assocPlus3 = ℚRing.solve-∀

sumRationalSubtractLocal :
  ∀ {A : Set} (values : List A) (f g : A → ℚ) →
  sumRational values (λ value → f value - g value)
  ≡ sumRational values f - sumRational values g
sumRationalSubtractLocal [] f g = ℚRing.solve-∀
sumRationalSubtractLocal (value ∷ values) f g
  rewrite sumRationalSubtractLocal values f g =
    Average.diffPlusDiff (f value) (g value)
      (sumRational values f) (sumRational values g)

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
      (λ site → diffMinus (left site) (right site) (test site)))
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
    axis fld →
  FieldEqual
    (Average.axisAverage dataSet
      (Average.axisAverage dataSet fld axis) axis)
    (Average.axisAverage dataSet fld axis)
axisAverageFixedPointwise dataSet axis fld site =
  Average.axisAverageIdempotent dataSet fld axis site

residualOrthogonalToAverage :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    fld axis →
  globalBlockInner
    (axisResidual dataSet fld axis)
    (Average.axisAverage dataSet fld axis)
  ≡ 0ℚ
residualOrthogonalToAverage dataSet fld axis =
  trans
    (innerSubtractLeft
      fld (Average.axisAverage dataSet fld axis)
      (Average.axisAverage dataSet fld axis))
    (trans
      (cong
        (λ value →
          globalBlockInner fld (Average.axisAverage dataSet fld axis)
          - value)
        (Average.axisAverageSelfAdjoint dataSet axis fld
          (Average.axisAverage dataSet fld axis)))
      (trans
        (cong
          (λ value →
            globalBlockInner fld (Average.axisAverage dataSet fld axis)
            - value)
          (innerRespectsRightPointwise fld
            (axisAverageFixedPointwise dataSet axis fld)))
        (OpaqueAlgebra.subtractSelfZero
          (globalBlockInner fld
            (Average.axisAverage dataSet fld axis)))))

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
        sq (left site) + (sq (right site)
        + (1ℚ + 1ℚ) * (left site * right site)))
      (λ site → sqBinomial (left site) (right site)))
    (trans
      (sumRationalAdd
        (physicalBlockSites L)
        (λ site → sq (left site))
        (λ site → sq (right site)
          + (1ℚ + 1ℚ) * (left site * right site)))
      (trans
        (cong (globalNormSq left +_)
          (sumRationalAdd
            (physicalBlockSites L)
            (λ site → sq (right site))
            (λ site → (1ℚ + 1ℚ) * (left site * right site))))
        (trans
          (cong (λ rest → globalNormSq left + (globalNormSq right + rest))
            (sumRationalScale
              (1ℚ + 1ℚ)
              (physicalBlockSites L)
              (λ site → left site * right site)))
          (assocPlus3
            (globalNormSq left)
            (globalNormSq right)
            ((1ℚ + 1ℚ) * globalBlockInner left right)))))

residualPlusAveragePointwise :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    fld axis →
  FieldEqual
    (addField
      (axisResidual dataSet fld axis)
      (Average.axisAverage dataSet fld axis))
    fld
residualPlusAveragePointwise dataSet fld axis site =
  OpaqueAlgebra.subtractAddCancel
    (fld site)
    (Average.axisAverage dataSet fld axis site)

axisAveragePythagoras :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    fld axis →
  globalNormSq fld
  ≡ globalNormSq (axisResidual dataSet fld axis)
    + globalNormSq (Average.axisAverage dataSet fld axis)
axisAveragePythagoras dataSet fld axis =
  trans
    (sym (globalNormRespectsPointwise
      (residualPlusAveragePointwise dataSet fld axis)))
    (trans
      (twoFieldSquareExpansion
        (axisResidual dataSet fld axis)
        (Average.axisAverage dataSet fld axis))
      (trans
        (cong
          (λ cross →
            globalNormSq (axisResidual dataSet fld axis)
            + globalNormSq (Average.axisAverage dataSet fld axis)
            + (1ℚ + 1ℚ) * cross)
          (residualOrthogonalToAverage dataSet fld axis))
        (OpaqueAlgebra.dropScaledZero
          (globalNormSq (axisResidual dataSet fld axis)
            + globalNormSq (Average.axisAverage dataSet fld axis))
          (1ℚ + 1ℚ))))

axisAverageNormContraction :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    fld axis →
  globalNormSq (Average.axisAverage dataSet fld axis)
  ≤ globalNormSq fld
axisAverageNormContraction dataSet fld axis =
  let
    pythagorasAverageFirst :
      globalNormSq fld
      ≡ globalNormSq (Average.axisAverage dataSet fld axis)
        + globalNormSq (axisResidual dataSet fld axis)
    pythagorasAverageFirst =
      trans
        (axisAveragePythagoras dataSet fld axis)
        (OpaqueAlgebra.swapSum
          (globalNormSq (axisResidual dataSet fld axis))
          (globalNormSq (Average.axisAverage dataSet fld axis)))
  in
  subst
    (λ upper →
      globalNormSq (Average.axisAverage dataSet fld axis) ≤ upper)
    (sym pythagorasAverageFirst)
    (baseBelowBasePlusRemainder
      (globalNormSq (Average.axisAverage dataSet fld axis))
      (globalNormSq (axisResidual dataSet fld axis))
      (globalNormSqNonnegative (axisResidual dataSet fld axis)))

normalizedAxisAveragePythagorasLevel : ProofLevel
normalizedAxisAveragePythagorasLevel = machineChecked
