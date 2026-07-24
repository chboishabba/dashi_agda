module DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
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
sumRationalSubtract [] left right = ℚRing.solve-∀
sumRationalSubtract (value ∷ values) left right
  rewrite sumRationalSubtract values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (sumRational values left) (sumRational values right)

axisAverage4Subtract : ∀ axis left right site →
  axisAverage4 (subtractField left right) axis site
  ≡ axisAverage4 left axis site - axisAverage4 right axis site
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
    (ℚRing.solve-∀
      quarter
      (physicalFibreSum left axis (axisTransverse axis site))
      (physicalFibreSum right axis (axisTransverse axis site)))

axisAverage4RespectsPointwise :
  ∀ axis {left right} →
  FieldEqual left right →
  FieldEqual (axisAverage4 left axis) (axisAverage4 right axis)
axisAverage4RespectsPointwise axis equality site =
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

projectedFixedPointwise : ∀ axis field →
  FieldEqual (axisAverage4 (axisAverage4 field axis) axis)
    (axisAverage4 field axis)
projectedFixedPointwise axis field site =
  axisAverage4Idempotent field axis site

commutingProjectPreservesFixedPointwise :
  ∀ fixedAxis movingAxis field →
  FieldEqual (axisAverage4 field fixedAxis) field →
  FieldEqual
    (axisAverage4 (axisAverage4 field movingAxis) fixedAxis)
    (axisAverage4 field movingAxis)
commutingProjectPreservesFixedPointwise fixedAxis movingAxis field fixed site =
  trans
    (axisAverage4Commutes fixedAxis movingAxis field site)
    (axisAverage4RespectsPointwise movingAxis fixed site)

commutingResidualPreservesFixedPointwise :
  ∀ fixedAxis residualAxis field →
  FieldEqual (axisAverage4 field fixedAxis) field →
  FieldEqual
    (axisAverage4 (subtractField field (axisAverage4 field residualAxis))
      fixedAxis)
    (subtractField field (axisAverage4 field residualAxis))
commutingResidualPreservesFixedPointwise
  fixedAxis residualAxis field fixed site =
  trans
    (axisAverage4Subtract fixedAxis field
      (axisAverage4 field residualAxis) site)
    (trans
      (cong
        (λ leftValue →
          leftValue
          - axisAverage4 (axisAverage4 field residualAxis) fixedAxis site)
        (fixed site))
      (trans
        (cong
          (λ rightValue → field site - rightValue)
          (axisAverage4Commutes fixedAxis residualAxis field site))
        (cong
          (λ rightValue → field site - rightValue)
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
      (λ site → ℚRing.solve-∀ (left site) (right site) (test site)))
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
  ∀ axis field fixedField →
  FieldEqual (axisAverage4 fixedField axis) fixedField →
  globalBlockInner
    (subtractField field (axisAverage4 field axis)) fixedField
  ≡ 0ℚ
residualOrthogonalToFixedPointwise axis field fixedField fixed =
  trans
    (innerSubtractLeft field (axisAverage4 field axis) fixedField)
    (trans
      (cong
        (λ value → globalBlockInner field fixedField - value)
        (physicalAxisAverage4SelfAdjoint axis field fixedField))
      (trans
        (cong
          (λ value → globalBlockInner field fixedField - value)
          (innerRespectsRightPointwise field fixed))
        (ℚRing.solve-∀ (globalBlockInner field fixedField))))

m1Fixed0 : ∀ field →
  FieldEqual (axisAverage4 (martingaleField1 field) zeroᵢ)
    (martingaleField1 field)
m1Fixed0 field =
  commutingResidualPreservesFixedPointwise
    zeroᵢ (sucᵢ zeroᵢ) (average0 field)
    (projectedFixedPointwise zeroᵢ field)

average01Fixed0 : ∀ field →
  FieldEqual (axisAverage4 (average01 field) zeroᵢ) (average01 field)
average01Fixed0 field =
  commutingProjectPreservesFixedPointwise
    zeroᵢ (sucᵢ zeroᵢ) (average0 field)
    (projectedFixedPointwise zeroᵢ field)

average012Fixed0 : ∀ field →
  FieldEqual (axisAverage4 (average012 field) zeroᵢ) (average012 field)
average012Fixed0 field =
  commutingProjectPreservesFixedPointwise
    zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) (average01 field)
    (average01Fixed0 field)

average012Fixed1 : ∀ field →
  FieldEqual (axisAverage4 (average012 field) (sucᵢ zeroᵢ))
    (average012 field)
average012Fixed1 field =
  commutingProjectPreservesFixedPointwise
    (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) (average01 field)
    (projectedFixedPointwise (sucᵢ zeroᵢ) (average0 field))

m2Fixed0 : ∀ field →
  FieldEqual (axisAverage4 (martingaleField2 field) zeroᵢ)
    (martingaleField2 field)
m2Fixed0 field =
  commutingResidualPreservesFixedPointwise
    zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) (average01 field)
    (average01Fixed0 field)

m2Fixed1 : ∀ field →
  FieldEqual (axisAverage4 (martingaleField2 field) (sucᵢ zeroᵢ))
    (martingaleField2 field)
m2Fixed1 field =
  commutingResidualPreservesFixedPointwise
    (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) (average01 field)
    (projectedFixedPointwise (sucᵢ zeroᵢ) (average0 field))

m3Fixed0 : ∀ field →
  FieldEqual (axisAverage4 (martingaleField3 field) zeroᵢ)
    (martingaleField3 field)
m3Fixed0 field =
  commutingResidualPreservesFixedPointwise
    zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (average012 field)
    (average012Fixed0 field)

m3Fixed1 : ∀ field →
  FieldEqual (axisAverage4 (martingaleField3 field) (sucᵢ zeroᵢ))
    (martingaleField3 field)
m3Fixed1 field =
  commutingResidualPreservesFixedPointwise
    (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (average012 field)
    (average012Fixed1 field)

m3Fixed2 : ∀ field →
  FieldEqual (axisAverage4 (martingaleField3 field)
    (sucᵢ (sucᵢ zeroᵢ)))
    (martingaleField3 field)
m3Fixed2 field =
  commutingResidualPreservesFixedPointwise
    (sucᵢ (sucᵢ zeroᵢ))
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (average012 field)
    (projectedFixedPointwise (sucᵢ (sucᵢ zeroᵢ)) (average01 field))

martingale01Zero : ∀ field →
  globalBlockInner (martingaleField0 field) (martingaleField1 field) ≡ 0ℚ
martingale01Zero field =
  residualOrthogonalToFixedPointwise zeroᵢ field
    (martingaleField1 field) (m1Fixed0 field)

martingale02Zero : ∀ field →
  globalBlockInner (martingaleField0 field) (martingaleField2 field) ≡ 0ℚ
martingale02Zero field =
  residualOrthogonalToFixedPointwise zeroᵢ field
    (martingaleField2 field) (m2Fixed0 field)

martingale03Zero : ∀ field →
  globalBlockInner (martingaleField0 field) (martingaleField3 field) ≡ 0ℚ
martingale03Zero field =
  residualOrthogonalToFixedPointwise zeroᵢ field
    (martingaleField3 field) (m3Fixed0 field)

martingale12Zero : ∀ field →
  globalBlockInner (martingaleField1 field) (martingaleField2 field) ≡ 0ℚ
martingale12Zero field =
  residualOrthogonalToFixedPointwise (sucᵢ zeroᵢ) (average0 field)
    (martingaleField2 field) (m2Fixed1 field)

martingale13Zero : ∀ field →
  globalBlockInner (martingaleField1 field) (martingaleField3 field) ≡ 0ℚ
martingale13Zero field =
  residualOrthogonalToFixedPointwise (sucᵢ zeroᵢ) (average0 field)
    (martingaleField3 field) (m3Fixed1 field)

martingale23Zero : ∀ field →
  globalBlockInner (martingaleField2 field) (martingaleField3 field) ≡ 0ℚ
martingale23Zero field =
  residualOrthogonalToFixedPointwise (sucᵢ (sucᵢ zeroᵢ)) (average01 field)
    (martingaleField3 field) (m3Fixed2 field)

path4PhysicalMartingaleOrthogonalityLevel : ProofLevel
path4PhysicalMartingaleOrthogonalityLevel = machineChecked
