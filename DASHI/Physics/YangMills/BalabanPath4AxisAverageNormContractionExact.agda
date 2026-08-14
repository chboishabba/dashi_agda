module DASHI.Physics.YangMills.BalabanPath4AxisAverageNormContractionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _≤_)
open import Data.Rational.Literals
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (Axis4)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; squareNonnegative; baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact

------------------------------------------------------------------------
-- A normalized coordinate average is an orthogonal projection on the literal
-- side-four block.  This module derives its L2 contraction from the already
-- proved self-adjointness and idempotence, rather than assuming Jensen again.
------------------------------------------------------------------------

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

globalNormSqNonnegative : ∀ siteField → 0ℚ ≤ globalNormSq siteField
globalNormSqNonnegative siteField =
  sumRationalNonnegative
    (physicalBlockSites side4)
    (λ site → sq (siteField site))
    (λ site → squareNonnegative (siteField site))

squareAddExact : ∀ a b →
  (a + b) * (a + b) ≡ a * a + (b * b + 2 * (a * b))
squareAddExact = ℚRing.solve-∀

subtractAddCancel : ∀ a b → (a + - b) + b ≡ a
subtractAddCancel = ℚRing.solve-∀

addZeroCrossCancel : ∀ a b → a + (b + 2 * 0ℚ) ≡ a + b
addZeroCrossCancel = ℚRing.solve-∀

addCommute : ∀ a b → a + b ≡ b + a
addCommute = ℚRing.solve-∀

twoFieldSquareExpansion : ∀ left right →
  globalNormSq (addField left right)
  ≡ globalNormSq left
    + (globalNormSq right + 2 * globalBlockInner left right)
twoFieldSquareExpansion left right =
  trans
    (sumRationalCong
      (physicalBlockSites side4)
      (λ site → (left site + right site) * (left site + right site))
      (λ site →
        left site * left site
        + (right site * right site
          + 2 * (left site * right site)))
      (λ site → squareAddExact (left site) (right site)))
    (trans
      (sumRationalAdd
        (physicalBlockSites side4)
        (λ site → left site * left site)
        (λ site → right site * right site
          + 2 * (left site * right site)))
      (cong (globalNormSq left +_)
        (trans
          (sumRationalAdd
            (physicalBlockSites side4)
            (λ site → right site * right site)
            (λ site → 2 * (left site * right site)))
          (cong (globalNormSq right +_)
            (sumRationalScale
              2
              (physicalBlockSites side4)
              (λ site → left site * right site))))))

axisResidual : SiteField side4 → Axis4 → SiteField side4
axisResidual siteField axis = subtractField siteField (axisAverage4 siteField axis)

axisResidualPlusAverage : ∀ siteField axis →
  FieldEqual
    (addField (axisResidual siteField axis) (axisAverage4 siteField axis))
    siteField
axisResidualPlusAverage siteField axis site =
  subtractAddCancel (siteField site) (axisAverage4 siteField axis site)

axisAveragePythagoras : ∀ siteField axis →
  globalNormSq siteField
  ≡ globalNormSq (axisResidual siteField axis)
    + globalNormSq (axisAverage4 siteField axis)
axisAveragePythagoras siteField axis =
  trans
    (sym (globalNormRespectsPointwise
      (axisResidualPlusAverage siteField axis)))
    (trans
      (twoFieldSquareExpansion
        (axisResidual siteField axis)
        (axisAverage4 siteField axis))
      (dropCross siteField axis))
  where
  dropCross : ∀ current currentAxis →
    globalNormSq (axisResidual current currentAxis)
      + (globalNormSq (axisAverage4 current currentAxis)
      + 2 * globalBlockInner
          (axisResidual current currentAxis)
          (axisAverage4 current currentAxis))
    ≡ globalNormSq (axisResidual current currentAxis)
      + globalNormSq (axisAverage4 current currentAxis)
  dropCross current currentAxis
    rewrite residualOrthogonalToFixedPointwise
      currentAxis current
      (axisAverage4 current currentAxis)
      (projectedFixedPointwise currentAxis current) =
    addZeroCrossCancel
      (globalNormSq (axisResidual current currentAxis))
      (globalNormSq (axisAverage4 current currentAxis))

axisAverageNormContraction : ∀ siteField axis →
  globalNormSq (axisAverage4 siteField axis) ≤ globalNormSq siteField
axisAverageNormContraction siteField axis =
  subst
    (λ upper → globalNormSq (axisAverage4 siteField axis) ≤ upper)
    (sym (averageFirstPythagoras siteField axis))
    (baseBelowBasePlusRemainder
      (globalNormSq (axisAverage4 siteField axis))
      (globalNormSq (axisResidual siteField axis))
      (globalNormSqNonnegative (axisResidual siteField axis)))
  where
  averageFirstPythagoras : ∀ current currentAxis →
    globalNormSq current
    ≡ globalNormSq (axisAverage4 current currentAxis)
      + globalNormSq (axisResidual current currentAxis)
  averageFirstPythagoras current currentAxis =
    trans
      (axisAveragePythagoras current currentAxis)
      (addCommute
        (globalNormSq (axisResidual current currentAxis))
        (globalNormSq (axisAverage4 current currentAxis)))

path4AxisAveragePythagorasLevel : ProofLevel
path4AxisAveragePythagorasLevel = machineChecked

path4AxisAverageNormContractionLevel : ProofLevel
path4AxisAverageNormContractionLevel = machineChecked
