module DASHI.Physics.YangMills.BalabanPath4AxisAverageNormContractionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
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

globalNormSqNonnegative : ∀ field → 0ℚ ≤ globalNormSq field
globalNormSqNonnegative field =
  sumRationalNonnegative
    (physicalBlockSites side4)
    (λ site → sq (field site))
    (λ site → squareNonnegative (field site))

twoFieldSquareExpansion : ∀ left right →
  globalNormSq (addField left right)
  ≡ globalNormSq left
    + (globalNormSq right + twoℚ * globalBlockInner left right)
twoFieldSquareExpansion left right =
  trans
    (sumRationalCong
      (physicalBlockSites side4)
      (λ site → sq (left site + right site))
      (λ site →
        sq (left site)
        + (sq (right site) + twoℚ * (left site * right site)))
      (λ site → ℚRing.solve-∀ (left site) (right site)))
    (trans
      (sumRationalAdd
        (physicalBlockSites side4)
        (λ site → sq (left site))
        (λ site → sq (right site) + twoℚ * (left site * right site)))
      (cong₂ _+_ refl
        (trans
          (sumRationalAdd
            (physicalBlockSites side4)
            (λ site → sq (right site))
            (λ site → twoℚ * (left site * right site)))
          (cong₂ _+_ refl
            (sumRationalScale
              twoℚ
              (physicalBlockSites side4)
              (λ site → left site * right site))))))

axisResidual : SiteField side4 → Axis4 → SiteField side4
axisResidual field axis = subtractField field (axisAverage4 field axis)

axisResidualPlusAverage : ∀ field axis →
  FieldEqual
    (addField (axisResidual field axis) (axisAverage4 field axis))
    field
axisResidualPlusAverage field axis site =
  ℚRing.solve-∀ (field site) (axisAverage4 field axis site)

axisAveragePythagoras : ∀ field axis →
  globalNormSq field
  ≡ globalNormSq (axisResidual field axis)
    + globalNormSq (axisAverage4 field axis)
axisAveragePythagoras field axis =
  trans
    (sym (globalNormRespectsPointwise
      (axisResidualPlusAverage field axis)))
    (trans
      (twoFieldSquareExpansion
        (axisResidual field axis)
        (axisAverage4 field axis))
      (dropCross field axis))
  where
  dropCross : ∀ current currentAxis →
    globalNormSq (axisResidual current currentAxis)
      + (globalNormSq (axisAverage4 current currentAxis)
      + twoℚ * globalBlockInner
          (axisResidual current currentAxis)
          (axisAverage4 current currentAxis))
    ≡ globalNormSq (axisResidual current currentAxis)
      + globalNormSq (axisAverage4 current currentAxis)
  dropCross current currentAxis
    rewrite residualOrthogonalToFixedPointwise
      currentAxis current
      (axisAverage4 current currentAxis)
      (projectedFixedPointwise currentAxis current) =
    ℚRing.solve-∀
      (globalNormSq (axisResidual current currentAxis))
      (globalNormSq (axisAverage4 current currentAxis))

axisAverageNormContraction : ∀ field axis →
  globalNormSq (axisAverage4 field axis) ≤ globalNormSq field
axisAverageNormContraction field axis =
  subst
    (λ upper → globalNormSq (axisAverage4 field axis) ≤ upper)
    (sym (averageFirstPythagoras field axis))
    (baseBelowBasePlusRemainder
      (globalNormSq (axisAverage4 field axis))
      (globalNormSq (axisResidual field axis))
      (globalNormSqNonnegative (axisResidual field axis)))
  where
  averageFirstPythagoras : ∀ current currentAxis →
    globalNormSq current
    ≡ globalNormSq (axisAverage4 current currentAxis)
      + globalNormSq (axisResidual current currentAxis)
  averageFirstPythagoras current currentAxis =
    trans
      (axisAveragePythagoras current currentAxis)
      (ℚRing.solve-∀
        (globalNormSq (axisResidual current currentAxis))
        (globalNormSq (axisAverage4 current currentAxis)))

path4AxisAveragePythagorasLevel : ProofLevel
path4AxisAveragePythagorasLevel = machineChecked

path4AxisAverageNormContractionLevel : ProofLevel
path4AxisAverageNormContractionLevel = machineChecked
