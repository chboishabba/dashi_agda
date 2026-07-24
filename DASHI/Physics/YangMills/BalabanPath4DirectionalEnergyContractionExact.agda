module DASHI.Physics.YangMills.BalabanPath4DirectionalEnergyContractionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; Positive; pos)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; fourℚ)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthAllCyclicIndices)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
open import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact using
  (sumRationalConstant)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageNormContractionExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalComponentPoincareExact using
  (axisDirectionalEnergy)

------------------------------------------------------------------------
-- Averaging in one coordinate contracts difference energy in every distinct
-- coordinate.  The proof proceeds on the literal side-four block:
--
--   * a coordinate average commutes pointwise with a distinct edge difference;
--   * the average is L2-contractive on the full site carrier;
--   * the full-site norm of a fixed-predecessor difference counts each physical
--     edge exactly four times;
--   * positivity of four cancels that exact multiplicity.
------------------------------------------------------------------------

side3 : Nat
side3 = suc (suc (suc zero))

twoLocal : ℚ
twoLocal = 1ℚ + 1ℚ

instance
  onePositive : Positive 1ℚ
  onePositive = pos

  twoLocalPositive : Positive twoLocal
  twoLocalPositive = ℚP.pos+pos⇒pos 1ℚ 1ℚ

  fourPositive : Positive fourℚ
  fourPositive = ℚP.pos+pos⇒pos twoLocal twoLocal

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

replaceAxis : ∀ {L} → Axis4 → CyclicIndex L → PhysicalBlockL L → PhysicalBlockL L
replaceAxis axis coordinate site =
  insertAxis axis coordinate (axisTransverse axis site)

edgeDifferenceField :
  SiteField side4 → Axis4 → CyclicIndex side3 → SiteField side4
edgeDifferenceField field axis predecessor site =
  field (replaceAxis axis (sucᵢ predecessor) site)
  - field (replaceAxis axis (weakenIndex predecessor) site)

axisAverageCommutesWithDistinctEdgeDifference :
  ∀ averageAxis differenceAxis field predecessor site →
  averageAxis ≢ differenceAxis →
  edgeDifferenceField (axisAverage4 field averageAxis)
    differenceAxis predecessor site
  ≡ axisAverage4 (edgeDifferenceField field differenceAxis predecessor)
      averageAxis site
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ zeroᵢ field predecessor site distinct = emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ zeroᵢ) field predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) field predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) zeroᵢ field predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) field predecessor site distinct =
  emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) field predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ field predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) field predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ zeroᵢ))
  field predecessor site distinct = emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  field predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ
  field predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ zeroᵢ)
  field predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ (sucᵢ zeroᵢ))
  field predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) field predecessor site distinct =
  emptyElim (distinct refl)

edgeDifferenceAveragePointwise :
  ∀ averageAxis differenceAxis field predecessor →
  averageAxis ≢ differenceAxis →
  FieldEqual
    (edgeDifferenceField (axisAverage4 field averageAxis)
      differenceAxis predecessor)
    (axisAverage4 (edgeDifferenceField field differenceAxis predecessor)
      averageAxis)
edgeDifferenceAveragePointwise averageAxis differenceAxis field predecessor distinct site =
  axisAverageCommutesWithDistinctEdgeDifference
    averageAxis differenceAxis field predecessor site distinct

fixedPredecessorNormContraction :
  ∀ averageAxis differenceAxis field predecessor →
  averageAxis ≢ differenceAxis →
  globalNormSq
    (edgeDifferenceField (axisAverage4 field averageAxis)
      differenceAxis predecessor)
  ≤ globalNormSq (edgeDifferenceField field differenceAxis predecessor)
fixedPredecessorNormContraction
  averageAxis differenceAxis field predecessor distinct =
  subst
    (λ leftNorm →
      leftNorm ≤ globalNormSq (edgeDifferenceField field differenceAxis predecessor))
    (sym (globalNormRespectsPointwise
      (edgeDifferenceAveragePointwise
        averageAxis differenceAxis field predecessor distinct)))
    (axisAverageNormContraction
      (edgeDifferenceField field differenceAxis predecessor)
      averageAxis)

edgeDifferenceAtTransverse :
  SiteField side4 → Axis4 → CyclicIndex side3 →
  Triple (CyclicIndex side4) → ℚ
edgeDifferenceAtTransverse field axis predecessor transverse =
  field (insertAxis axis (sucᵢ predecessor) transverse)
  - field (insertAxis axis (weakenIndex predecessor) transverse)

edgeDifferenceOnInsertedAxis :
  ∀ field axis predecessor coordinate transverse →
  edgeDifferenceField field axis predecessor
    (insertAxis axis coordinate transverse)
  ≡ edgeDifferenceAtTransverse field axis predecessor transverse
edgeDifferenceOnInsertedAxis field axis predecessor coordinate transverse
  rewrite extractInsertTransverse axis coordinate transverse = refl

axisPredecessorEnergy :
  Axis4 → SiteField side4 → CyclicIndex side3 → ℚ
axisPredecessorEnergy axis field predecessor =
  sumRational (physicalTransverseCoordinates side4)
    (λ transverse → sq (edgeDifferenceAtTransverse field axis predecessor transverse))

fibreMultiplicityFour : ∀ field axis predecessor transverse →
  sumRational (allCyclicIndices side4)
    (λ coordinate →
      sq (edgeDifferenceField field axis predecessor
        (insertAxis axis coordinate transverse)))
  ≡ fourℚ * sq (edgeDifferenceAtTransverse field axis predecessor transverse)
fibreMultiplicityFour field axis predecessor transverse =
  trans
    (sumRationalCong
      (allCyclicIndices side4)
      (λ coordinate →
        sq (edgeDifferenceField field axis predecessor
          (insertAxis axis coordinate transverse)))
      (λ coordinate →
        sq (edgeDifferenceAtTransverse field axis predecessor transverse))
      (λ coordinate →
        cong sq (edgeDifferenceOnInsertedAxis
          field axis predecessor coordinate transverse)))
    (trans
      (sumRationalConstant
        (allCyclicIndices side4)
        (sq (edgeDifferenceAtTransverse field axis predecessor transverse)))
      (lengthFour field axis predecessor transverse))
  where
  lengthFour : ∀ current currentAxis currentPredecessor currentTransverse →
    natAsRational (length (allCyclicIndices side4))
      * sq (edgeDifferenceAtTransverse
          current currentAxis currentPredecessor currentTransverse)
    ≡ fourℚ * sq (edgeDifferenceAtTransverse
          current currentAxis currentPredecessor currentTransverse)
  lengthFour current currentAxis currentPredecessor currentTransverse
    rewrite lengthAllCyclicIndices side4 = ℚRing.solve-∀
      (sq (edgeDifferenceAtTransverse
        current currentAxis currentPredecessor currentTransverse))

globalEdgeDifferenceNormFourfold : ∀ field axis predecessor →
  globalNormSq (edgeDifferenceField field axis predecessor)
  ≡ fourℚ * axisPredecessorEnergy axis field predecessor
globalEdgeDifferenceNormFourfold field axis predecessor =
  trans
    (sym (axisPartitionSumMatchesGlobal axis
      (λ site → sq (edgeDifferenceField field axis predecessor site))))
    (trans
      (sumRationalCong
        (physicalTransverseCoordinates side4)
        (λ transverse →
          sumRational (allCyclicIndices side4)
            (λ coordinate →
              sq (edgeDifferenceField field axis predecessor
                (insertAxis axis coordinate transverse))))
        (λ transverse →
          fourℚ * sq (edgeDifferenceAtTransverse
            field axis predecessor transverse))
        (fibreMultiplicityFour field axis predecessor))
      (sumRationalScale
        fourℚ
        (physicalTransverseCoordinates side4)
        (λ transverse →
          sq (edgeDifferenceAtTransverse field axis predecessor transverse))))

axisDirectionalEnergyAsPredecessorSum : ∀ axis field →
  axisDirectionalEnergy axis field
  ≡ sumRational (allCyclicIndices side3)
      (axisPredecessorEnergy axis field)
axisDirectionalEnergyAsPredecessorSum axis field =
  sumSwap
    (physicalTransverseCoordinates side4)
    (allCyclicIndices side3)
    (λ transverse predecessor →
      sq (edgeDifferenceAtTransverse field axis predecessor transverse))

sumRationalMonotone :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  sumRational values left ≤ sumRational values right
sumRationalMonotone [] left right pointwise = ℚP.≤-refl
sumRationalMonotone (value ∷ values) left right pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumRationalMonotone values left right pointwise)

predecessorNormSumExact : ∀ field axis →
  sumRational (allCyclicIndices side3)
    (λ predecessor → globalNormSq (edgeDifferenceField field axis predecessor))
  ≡ fourℚ * axisDirectionalEnergy axis field
predecessorNormSumExact field axis =
  trans
    (sumRationalCong
      (allCyclicIndices side3)
      (λ predecessor → globalNormSq (edgeDifferenceField field axis predecessor))
      (λ predecessor → fourℚ * axisPredecessorEnergy axis field predecessor)
      (globalEdgeDifferenceNormFourfold field axis))
    (trans
      (sumRationalScale
        fourℚ
        (allCyclicIndices side3)
        (axisPredecessorEnergy axis field))
      (cong (fourℚ *_)
        (sym (axisDirectionalEnergyAsPredecessorSum axis field))))

fourTimesDirectionalEnergyContraction :
  ∀ averageAxis differenceAxis field →
  averageAxis ≢ differenceAxis →
  fourℚ * axisDirectionalEnergy differenceAxis (axisAverage4 field averageAxis)
  ≤ fourℚ * axisDirectionalEnergy differenceAxis field
fourTimesDirectionalEnergyContraction averageAxis differenceAxis field distinct =
  subst
    (λ leftValue →
      leftValue ≤ fourℚ * axisDirectionalEnergy differenceAxis field)
    (predecessorNormSumExact (axisAverage4 field averageAxis) differenceAxis)
    (subst
      (λ rightValue →
        sumRational (allCyclicIndices side3)
          (λ predecessor →
            globalNormSq
              (edgeDifferenceField (axisAverage4 field averageAxis)
                differenceAxis predecessor))
        ≤ rightValue)
      (predecessorNormSumExact field differenceAxis)
      (sumRationalMonotone
        (allCyclicIndices side3)
        (λ predecessor →
          globalNormSq
            (edgeDifferenceField (axisAverage4 field averageAxis)
              differenceAxis predecessor))
        (λ predecessor →
          globalNormSq (edgeDifferenceField field differenceAxis predecessor))
        (λ predecessor →
          fixedPredecessorNormContraction
            averageAxis differenceAxis field predecessor distinct)))

distinctAxisDirectionalEnergyContraction :
  ∀ averageAxis differenceAxis field →
  averageAxis ≢ differenceAxis →
  axisDirectionalEnergy differenceAxis (axisAverage4 field averageAxis)
  ≤ axisDirectionalEnergy differenceAxis field
distinctAxisDirectionalEnergyContraction
  averageAxis differenceAxis field distinct =
  ℚP.*-cancelˡ-≤-pos fourℚ
    (fourTimesDirectionalEnergyContraction
      averageAxis differenceAxis field distinct)

path4DistinctAxisDifferenceCommutationLevel : ProofLevel
path4DistinctAxisDifferenceCommutationLevel = computed

path4DistinctAxisDirectionalEnergyContractionLevel : ProofLevel
path4DistinctAxisDirectionalEnergyContractionLevel = machineChecked
