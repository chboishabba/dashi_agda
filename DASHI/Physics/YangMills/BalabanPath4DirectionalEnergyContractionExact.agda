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
edgeDifferenceField siteField axis predecessor site =
  siteField (replaceAxis axis (sucᵢ predecessor) site)
  - siteField (replaceAxis axis (weakenIndex predecessor) site)

axisAverageCommutesWithDistinctEdgeDifference :
  ∀ averageAxis differenceAxis siteField predecessor site →
  averageAxis ≢ differenceAxis →
  edgeDifferenceField (axisAverage4 siteField averageAxis)
    differenceAxis predecessor site
  ≡ axisAverage4 (edgeDifferenceField siteField differenceAxis predecessor)
      averageAxis site
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ zeroᵢ siteField predecessor site distinct = emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ zeroᵢ) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) zeroᵢ siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) siteField predecessor site distinct =
  emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ zeroᵢ))
  siteField predecessor site distinct = emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  siteField predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ
  siteField predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ zeroᵢ)
  siteField predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ (sucᵢ zeroᵢ))
  siteField predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField predecessor site distinct =
  emptyElim (distinct refl)

edgeDifferenceAveragePointwise :
  ∀ averageAxis differenceAxis siteField predecessor →
  averageAxis ≢ differenceAxis →
  FieldEqual
    (edgeDifferenceField (axisAverage4 siteField averageAxis)
      differenceAxis predecessor)
    (axisAverage4 (edgeDifferenceField siteField differenceAxis predecessor)
      averageAxis)
edgeDifferenceAveragePointwise averageAxis differenceAxis siteField predecessor distinct site =
  axisAverageCommutesWithDistinctEdgeDifference
    averageAxis differenceAxis siteField predecessor site distinct

fixedPredecessorNormContraction :
  ∀ averageAxis differenceAxis siteField predecessor →
  averageAxis ≢ differenceAxis →
  globalNormSq
    (edgeDifferenceField (axisAverage4 siteField averageAxis)
      differenceAxis predecessor)
  ≤ globalNormSq (edgeDifferenceField siteField differenceAxis predecessor)
fixedPredecessorNormContraction
  averageAxis differenceAxis siteField predecessor distinct =
  subst
    (λ leftNorm →
      leftNorm ≤ globalNormSq (edgeDifferenceField siteField differenceAxis predecessor))
    (sym (globalNormRespectsPointwise
      (edgeDifferenceAveragePointwise
        averageAxis differenceAxis siteField predecessor distinct)))
    (axisAverageNormContraction
      (edgeDifferenceField siteField differenceAxis predecessor)
      averageAxis)

edgeDifferenceAtTransverse :
  SiteField side4 → Axis4 → CyclicIndex side3 →
  Triple (CyclicIndex side4) → ℚ
edgeDifferenceAtTransverse siteField axis predecessor transverse =
  siteField (insertAxis axis (sucᵢ predecessor) transverse)
  - siteField (insertAxis axis (weakenIndex predecessor) transverse)

edgeDifferenceOnInsertedAxis :
  ∀ siteField axis predecessor coordinate transverse →
  edgeDifferenceField siteField axis predecessor
    (insertAxis axis coordinate transverse)
  ≡ edgeDifferenceAtTransverse siteField axis predecessor transverse
edgeDifferenceOnInsertedAxis siteField axis predecessor coordinate transverse
  rewrite extractInsertTransverse axis coordinate transverse = refl

axisPredecessorEnergy :
  Axis4 → SiteField side4 → CyclicIndex side3 → ℚ
axisPredecessorEnergy axis siteField predecessor =
  sumRational (physicalTransverseCoordinates side4)
    (λ transverse → sq (edgeDifferenceAtTransverse siteField axis predecessor transverse))

fibreMultiplicityFour : ∀ siteField axis predecessor transverse →
  sumRational (allCyclicIndices side4)
    (λ coordinate →
      sq (edgeDifferenceField siteField axis predecessor
        (insertAxis axis coordinate transverse)))
  ≡ fourℚ * sq (edgeDifferenceAtTransverse siteField axis predecessor transverse)
fibreMultiplicityFour siteField axis predecessor transverse =
  trans
    (sumRationalCong
      (allCyclicIndices side4)
      (λ coordinate →
        sq (edgeDifferenceField siteField axis predecessor
          (insertAxis axis coordinate transverse)))
      (λ coordinate →
        sq (edgeDifferenceAtTransverse siteField axis predecessor transverse))
      (λ coordinate →
        cong sq (edgeDifferenceOnInsertedAxis
          siteField axis predecessor coordinate transverse)))
    (trans
      (sumRationalConstant
        (allCyclicIndices side4)
        (sq (edgeDifferenceAtTransverse siteField axis predecessor transverse)))
      (lengthFour siteField axis predecessor transverse))
  where
  lengthFour : ∀ current currentAxis currentPredecessor currentTransverse →
    natAsRational (length (allCyclicIndices side4))
      * sq (edgeDifferenceAtTransverse
          current currentAxis currentPredecessor currentTransverse)
    ≡ fourℚ * sq (edgeDifferenceAtTransverse
          current currentAxis currentPredecessor currentTransverse)
  lengthFour current currentAxis currentPredecessor currentTransverse
    rewrite lengthAllCyclicIndices side4 = ℚRing.solve-∀

globalEdgeDifferenceNormFourfold : ∀ siteField axis predecessor →
  globalNormSq (edgeDifferenceField siteField axis predecessor)
  ≡ fourℚ * axisPredecessorEnergy axis siteField predecessor
globalEdgeDifferenceNormFourfold siteField axis predecessor =
  trans
    (sym (axisPartitionSumMatchesGlobal axis
      (λ site → sq (edgeDifferenceField siteField axis predecessor site))))
    (trans
      (sumRationalCong
        (physicalTransverseCoordinates side4)
        (λ transverse →
          sumRational (allCyclicIndices side4)
            (λ coordinate →
              sq (edgeDifferenceField siteField axis predecessor
                (insertAxis axis coordinate transverse))))
        (λ transverse →
          fourℚ * sq (edgeDifferenceAtTransverse
            siteField axis predecessor transverse))
        (fibreMultiplicityFour siteField axis predecessor))
      (sumRationalScale
        fourℚ
        (physicalTransverseCoordinates side4)
        (λ transverse →
          sq (edgeDifferenceAtTransverse siteField axis predecessor transverse))))

axisDirectionalEnergyAsPredecessorSum : ∀ axis siteField →
  axisDirectionalEnergy axis siteField
  ≡ sumRational (allCyclicIndices side3)
      (axisPredecessorEnergy axis siteField)
axisDirectionalEnergyAsPredecessorSum axis siteField =
  sumSwap
    (physicalTransverseCoordinates side4)
    (allCyclicIndices side3)
    (λ transverse predecessor →
      sq (edgeDifferenceAtTransverse siteField axis predecessor transverse))

sumRationalMonotone :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  sumRational values left ≤ sumRational values right
sumRationalMonotone [] left right pointwise = ℚP.≤-refl
sumRationalMonotone (value ∷ values) left right pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumRationalMonotone values left right pointwise)

predecessorNormSumExact : ∀ siteField axis →
  sumRational (allCyclicIndices side3)
    (λ predecessor → globalNormSq (edgeDifferenceField siteField axis predecessor))
  ≡ fourℚ * axisDirectionalEnergy axis siteField
predecessorNormSumExact siteField axis =
  trans
    (sumRationalCong
      (allCyclicIndices side3)
      (λ predecessor → globalNormSq (edgeDifferenceField siteField axis predecessor))
      (λ predecessor → fourℚ * axisPredecessorEnergy axis siteField predecessor)
      (globalEdgeDifferenceNormFourfold siteField axis))
    (trans
      (sumRationalScale
        fourℚ
        (allCyclicIndices side3)
        (axisPredecessorEnergy axis siteField))
      (cong (fourℚ *_)
        (sym (axisDirectionalEnergyAsPredecessorSum axis siteField))))

fourTimesDirectionalEnergyContraction :
  ∀ averageAxis differenceAxis siteField →
  averageAxis ≢ differenceAxis →
  fourℚ * axisDirectionalEnergy differenceAxis (axisAverage4 siteField averageAxis)
  ≤ fourℚ * axisDirectionalEnergy differenceAxis siteField
fourTimesDirectionalEnergyContraction averageAxis differenceAxis siteField distinct =
  subst
    (λ leftValue →
      leftValue ≤ fourℚ * axisDirectionalEnergy differenceAxis siteField)
    (predecessorNormSumExact (axisAverage4 siteField averageAxis) differenceAxis)
    (subst
      (λ rightValue →
        sumRational (allCyclicIndices side3)
          (λ predecessor →
            globalNormSq
              (edgeDifferenceField (axisAverage4 siteField averageAxis)
                differenceAxis predecessor))
        ≤ rightValue)
      (predecessorNormSumExact siteField differenceAxis)
      (sumRationalMonotone
        (allCyclicIndices side3)
        (λ predecessor →
          globalNormSq
            (edgeDifferenceField (axisAverage4 siteField averageAxis)
              differenceAxis predecessor))
        (λ predecessor →
          globalNormSq (edgeDifferenceField siteField differenceAxis predecessor))
        (λ predecessor →
          fixedPredecessorNormContraction
            averageAxis differenceAxis siteField predecessor distinct)))

distinctAxisDirectionalEnergyContraction :
  ∀ averageAxis differenceAxis siteField →
  averageAxis ≢ differenceAxis →
  axisDirectionalEnergy differenceAxis (axisAverage4 siteField averageAxis)
  ≤ axisDirectionalEnergy differenceAxis siteField
distinctAxisDirectionalEnergyContraction
  averageAxis differenceAxis siteField distinct =
  ℚP.*-cancelˡ-≤-pos fourℚ
    (fourTimesDirectionalEnergyContraction
      averageAxis differenceAxis siteField distinct)

path4DistinctAxisDifferenceCommutationLevel : ProofLevel
path4DistinctAxisDifferenceCommutationLevel = computed

path4DistinctAxisDirectionalEnergyContractionLevel : ProofLevel
path4DistinctAxisDirectionalEnergyContractionLevel = machineChecked
