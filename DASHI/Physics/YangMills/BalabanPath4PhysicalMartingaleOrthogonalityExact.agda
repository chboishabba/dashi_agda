module DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
  using (insertAxis; axisTransverse; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact

------------------------------------------------------------------------
-- Literal orthogonality of the four side-four coordinate martingales.
-- Function extensionality is not required: all state equalities are pointwise.
------------------------------------------------------------------------

FieldEqual : SiteField side4 → SiteField side4 → Set
FieldEqual left right = ∀ site → left site ≡ right site

subtractField : SiteField side4 → SiteField side4 → SiteField side4
subtractField left right site = left site - right site

sumRationalSubtract :
  ∀ {A : Set} values (left right : A → ℚ) →
  sumRational values (λ value → left value - right value)
  ≡ sumRational values left - sumRational values right
subtractPlusPlus : ∀ a b c d →
  (a - b) + (c - d) ≡ (a + c) - (b + d)
subtractPlusPlus = ℚRing.solve-∀
sumRationalSubtract [] left right = ℚRing.solve-∀
sumRationalSubtract (value ∷ values) left right
  rewrite sumRationalSubtract values left right =
  subtractPlusPlus
    (left value)
    (right value)
    (sumRational values left)
    (sumRational values right)

axisAverage4Subtract : ∀ axis left right site →
  axisAverage4 (subtractField left right) axis site
  ≡ axisAverage4 left axis site - axisAverage4 right axis site
scaleSubtract : ∀ scale left right →
  scale * (left - right) ≡ scale * left - scale * right
scaleSubtract = ℚRing.solve-∀
axisAverage4Subtract axis left right site =
  trans
    (cong
      (λ fibreTotal → quarter * fibreTotal)
      (sumRationalSubtract
        (allCyclicIndices side4)
        (λ coordinate →
          left (insertAxis axis coordinate (axisTransverse axis site)))
        (λ coordinate →
          right (insertAxis axis coordinate (axisTransverse axis site)))))
    (scaleSubtract
      quarter
      (physicalFibreSum left axis (axisTransverse axis site))
      (physicalFibreSum right axis (axisTransverse axis site)))

axisAverage4RespectsPointwise :
  ∀ axis {left right} →
  FieldEqual left right →
  FieldEqual (axisAverage4 left axis) (axisAverage4 right axis)
axisAverage4RespectsPointwise axis {left} {right} equality site =
  cong
    (λ fibreTotal → quarter * fibreTotal)
    (sumRationalCong
      (allCyclicIndices side4)
      (λ coordinate →
        left (insertAxis axis coordinate (axisTransverse axis site)))
      (λ coordinate →
        right (insertAxis axis coordinate (axisTransverse axis site)))
      (λ coordinate →
        equality (insertAxis axis coordinate (axisTransverse axis site))))

projectedFixedPointwise : ∀ axis siteField →
  FieldEqual (axisAverage4 (axisAverage4 siteField axis) axis)
    (axisAverage4 siteField axis)
projectedFixedPointwise axis siteField site =
  axisAverage4Idempotent siteField axis site

commutingProjectPreservesFixedPointwise :
  ∀ fixedAxis movingAxis siteField →
  FieldEqual (axisAverage4 siteField fixedAxis) siteField →
  FieldEqual
    (axisAverage4 (axisAverage4 siteField movingAxis) fixedAxis)
    (axisAverage4 siteField movingAxis)
commutingProjectPreservesFixedPointwise fixedAxis movingAxis siteField fixed site =
  trans
    (sym (axisAverage4Commutes fixedAxis movingAxis siteField site))
    (axisAverage4RespectsPointwise movingAxis fixed site)

commutingResidualPreservesFixedPointwise :
  ∀ fixedAxis residualAxis siteField →
  FieldEqual (axisAverage4 siteField fixedAxis) siteField →
  FieldEqual
    (axisAverage4 (subtractField siteField (axisAverage4 siteField residualAxis))
      fixedAxis)
    (subtractField siteField (axisAverage4 siteField residualAxis))
commutingResidualPreservesFixedPointwise
  fixedAxis residualAxis siteField fixed site =
  trans
    (axisAverage4Subtract fixedAxis siteField
      (axisAverage4 siteField residualAxis) site)
    (trans
      (cong
        (λ leftValue →
          leftValue
          - axisAverage4 (axisAverage4 siteField residualAxis) fixedAxis site)
        (fixed site))
      (trans
      (cong
          (λ rightValue → siteField site - rightValue)
          (sym (axisAverage4Commutes fixedAxis residualAxis siteField site)))
        (cong
          (λ rightValue → siteField site - rightValue)
          (axisAverage4RespectsPointwise residualAxis fixed site))))

innerSubtractLeft : ∀ left right test →
  globalBlockInner (subtractField left right) test
  ≡ globalBlockInner left test - globalBlockInner right test
innerSubtractLeft left right test =
  trans
    (sumRationalCong
      (physicalBlockSites side4)
      (λ site → (left site - right site) * test site)
      (λ site → left site * test site - right site * test site)
      (λ site →
        trans
          (ℚP.*-comm (left site - right site) (test site))
          (trans
            (ℚP.*-distribˡ-+ (test site) (left site) (- (right site)))
            (trans
              (cong₂ _+_
                (ℚP.*-comm (test site) (left site))
                (trans
                  (ℚP.*-comm (test site) (- (right site)))
                  (sym (ℚP.neg-distribˡ-* (right site) (test site)))))
              refl))))
    (sumRationalSubtract
      (physicalBlockSites side4)
      (λ site → left site * test site)
      (λ site → right site * test site))

innerRespectsRightPointwise :
  ∀ left {right right′} →
  FieldEqual right right′ →
  globalBlockInner left right ≡ globalBlockInner left right′
innerRespectsRightPointwise left {right} {right′} equality =
  sumRationalCong
    (physicalBlockSites side4)
    (λ site → left site * right site)
    (λ site → left site * right′ site)
    (λ site → cong (λ value → left site * value) (equality site))

residualOrthogonalToFixedPointwise :
  ∀ axis siteField fixedField →
  FieldEqual (axisAverage4 fixedField axis) fixedField →
  globalBlockInner
    (subtractField siteField (axisAverage4 siteField axis)) fixedField
  ≡ 0ℚ
residualOrthogonalToFixedPointwise axis siteField fixedField fixed =
  trans
    (innerSubtractLeft siteField (axisAverage4 siteField axis) fixedField)
    (trans
      (cong
        (λ value → globalBlockInner siteField fixedField - value)
        (physicalAxisAverage4SelfAdjoint axis siteField fixedField))
      (trans
        (cong
          (λ value → globalBlockInner siteField fixedField - value)
          (innerRespectsRightPointwise siteField fixed))
        (ℚP.+-inverseʳ (globalBlockInner siteField fixedField))))

m1Fixed0 : ∀ siteField →
  FieldEqual (axisAverage4 (martingaleField1 siteField) zeroᵢ)
    (martingaleField1 siteField)
m1Fixed0 siteField =
  commutingResidualPreservesFixedPointwise
    zeroᵢ (sucᵢ zeroᵢ) (average0 siteField)
    (projectedFixedPointwise zeroᵢ siteField)

average01Fixed0 : ∀ siteField →
  FieldEqual (axisAverage4 (average01 siteField) zeroᵢ) (average01 siteField)
average01Fixed0 siteField =
  commutingProjectPreservesFixedPointwise
    zeroᵢ (sucᵢ zeroᵢ) (average0 siteField)
    (projectedFixedPointwise zeroᵢ siteField)

average012Fixed0 : ∀ siteField →
  FieldEqual (axisAverage4 (average012 siteField) zeroᵢ) (average012 siteField)
average012Fixed0 siteField =
  commutingProjectPreservesFixedPointwise
    zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) (average01 siteField)
    (average01Fixed0 siteField)

average012Fixed1 : ∀ siteField →
  FieldEqual (axisAverage4 (average012 siteField) (sucᵢ zeroᵢ))
    (average012 siteField)
average012Fixed1 siteField =
  commutingProjectPreservesFixedPointwise
    (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) (average01 siteField)
    (projectedFixedPointwise (sucᵢ zeroᵢ) (average0 siteField))

m2Fixed0 : ∀ siteField →
  FieldEqual (axisAverage4 (martingaleField2 siteField) zeroᵢ)
    (martingaleField2 siteField)
m2Fixed0 siteField =
  commutingResidualPreservesFixedPointwise
    zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) (average01 siteField)
    (average01Fixed0 siteField)

m2Fixed1 : ∀ siteField →
  FieldEqual (axisAverage4 (martingaleField2 siteField) (sucᵢ zeroᵢ))
    (martingaleField2 siteField)
m2Fixed1 siteField =
  commutingResidualPreservesFixedPointwise
    (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) (average01 siteField)
    (projectedFixedPointwise (sucᵢ zeroᵢ) (average0 siteField))

m3Fixed0 : ∀ siteField →
  FieldEqual (axisAverage4 (martingaleField3 siteField) zeroᵢ)
    (martingaleField3 siteField)
m3Fixed0 siteField =
  commutingResidualPreservesFixedPointwise
    zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (average012 siteField)
    (average012Fixed0 siteField)

m3Fixed1 : ∀ siteField →
  FieldEqual (axisAverage4 (martingaleField3 siteField) (sucᵢ zeroᵢ))
    (martingaleField3 siteField)
m3Fixed1 siteField =
  commutingResidualPreservesFixedPointwise
    (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (average012 siteField)
    (average012Fixed1 siteField)

m3Fixed2 : ∀ siteField →
  FieldEqual (axisAverage4 (martingaleField3 siteField)
    (sucᵢ (sucᵢ zeroᵢ)))
    (martingaleField3 siteField)
m3Fixed2 siteField =
  commutingResidualPreservesFixedPointwise
    (sucᵢ (sucᵢ zeroᵢ))
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (average012 siteField)
    (projectedFixedPointwise (sucᵢ (sucᵢ zeroᵢ)) (average01 siteField))

martingale01Zero : ∀ siteField →
  globalBlockInner (martingaleField0 siteField) (martingaleField1 siteField) ≡ 0ℚ
martingale01Zero siteField =
  residualOrthogonalToFixedPointwise zeroᵢ siteField
    (martingaleField1 siteField) (m1Fixed0 siteField)

martingale02Zero : ∀ siteField →
  globalBlockInner (martingaleField0 siteField) (martingaleField2 siteField) ≡ 0ℚ
martingale02Zero siteField =
  residualOrthogonalToFixedPointwise zeroᵢ siteField
    (martingaleField2 siteField) (m2Fixed0 siteField)

martingale03Zero : ∀ siteField →
  globalBlockInner (martingaleField0 siteField) (martingaleField3 siteField) ≡ 0ℚ
martingale03Zero siteField =
  residualOrthogonalToFixedPointwise zeroᵢ siteField
    (martingaleField3 siteField) (m3Fixed0 siteField)

martingale12Zero : ∀ siteField →
  globalBlockInner (martingaleField1 siteField) (martingaleField2 siteField) ≡ 0ℚ
martingale12Zero siteField =
  residualOrthogonalToFixedPointwise (sucᵢ zeroᵢ) (average0 siteField)
    (martingaleField2 siteField) (m2Fixed1 siteField)

martingale13Zero : ∀ siteField →
  globalBlockInner (martingaleField1 siteField) (martingaleField3 siteField) ≡ 0ℚ
martingale13Zero siteField =
  residualOrthogonalToFixedPointwise (sucᵢ zeroᵢ) (average0 siteField)
    (martingaleField3 siteField) (m3Fixed1 siteField)

martingale23Zero : ∀ siteField →
  globalBlockInner (martingaleField2 siteField) (martingaleField3 siteField) ≡ 0ℚ
martingale23Zero siteField =
  residualOrthogonalToFixedPointwise (sucᵢ (sucᵢ zeroᵢ)) (average01 siteField)
    (martingaleField3 siteField) (m3Fixed2 siteField)

path4PhysicalMartingaleOrthogonalityExactLevel : ProofLevel
path4PhysicalMartingaleOrthogonalityExactLevel = machineChecked
