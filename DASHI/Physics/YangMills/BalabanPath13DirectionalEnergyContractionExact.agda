module DASHI.Physics.YangMills.BalabanPath13DirectionalEnergyContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01240221.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Source-scale replacement for the old side-four directional contraction.
-- On the literal side-13 block a normalized average in one coordinate
-- contracts open-edge energy in every distinct coordinate.  The proof uses
-- exact commutation with a fixed edge difference, global L2 contraction of
-- the normalized projection, and the literal multiplicity thirteen of each
-- transverse edge when expanded over the full site carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational using
  (ℚ; _+_; _-_; _*_; _≤_; _/_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthAllCyclicIndices)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
open import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact using
  (sumRationalConstant)
open import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact
import DASHI.Physics.YangMills.BalabanNormalizedAxisAverageExact as Average
import DASHI.Physics.YangMills.BalabanNormalizedAxisAverageNormContractionExact as Norm
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13

side12 : Nat
side12 = 12

thirteenℚ : ℚ
thirteenℚ = + 13 / 1

instance
  thirteenPositive : Positive thirteenℚ
  thirteenPositive = ℚP.normalize-pos 13 1

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

replaceAxis : Axis4 → CyclicIndex Side13.side13 →
  PhysicalBlockL Side13.side13 → PhysicalBlockL Side13.side13
replaceAxis axis coordinate site =
  insertAxis axis coordinate (axisTransverse axis site)

edgeDifferenceField :
  SiteField Side13.side13 → Axis4 → CyclicIndex side12 →
  SiteField Side13.side13
edgeDifferenceField field axis predecessor site =
  field (replaceAxis axis (sucᵢ predecessor) site)
  - field (replaceAxis axis (weakenIndex predecessor) site)

axisAverageCommutesWithDistinctEdgeDifference :
  ∀ averageAxis differenceAxis field predecessor site →
  averageAxis ≢ differenceAxis →
  edgeDifferenceField
    (Average.axisAverage Side13.side13AverageData field averageAxis)
    differenceAxis predecessor site
  ≡ Average.axisAverage Side13.side13AverageData
      (edgeDifferenceField field differenceAxis predecessor)
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
  Norm.FieldEqual
    (edgeDifferenceField
      (Average.axisAverage Side13.side13AverageData field averageAxis)
      differenceAxis predecessor)
    (Average.axisAverage Side13.side13AverageData
      (edgeDifferenceField field differenceAxis predecessor) averageAxis)
edgeDifferenceAveragePointwise averageAxis differenceAxis field predecessor distinct site =
  axisAverageCommutesWithDistinctEdgeDifference
    averageAxis differenceAxis field predecessor site distinct

fixedPredecessorNormContraction :
  ∀ averageAxis differenceAxis field predecessor →
  averageAxis ≢ differenceAxis →
  Norm.globalNormSq
    (edgeDifferenceField
      (Average.axisAverage Side13.side13AverageData field averageAxis)
      differenceAxis predecessor)
  ≤ Norm.globalNormSq (edgeDifferenceField field differenceAxis predecessor)
fixedPredecessorNormContraction averageAxis differenceAxis field predecessor distinct =
  subst
    (λ leftNorm →
      leftNorm ≤ Norm.globalNormSq (edgeDifferenceField field differenceAxis predecessor))
    (sym (Norm.globalNormRespectsPointwise
      (edgeDifferenceAveragePointwise
        averageAxis differenceAxis field predecessor distinct)))
    (Norm.axisAverageNormContraction Side13.side13AverageData
      (edgeDifferenceField field differenceAxis predecessor) averageAxis)

edgeDifferenceAtTransverse :
  SiteField Side13.side13 → Axis4 → CyclicIndex side12 →
  Triple (CyclicIndex Side13.side13) → ℚ
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
  Axis4 → SiteField Side13.side13 → CyclicIndex side12 → ℚ
axisPredecessorEnergy axis field predecessor =
  sumRational (physicalTransverseCoordinates Side13.side13)
    (λ transverse → sq (edgeDifferenceAtTransverse field axis predecessor transverse))

fibreMultiplicityThirteen : ∀ field axis predecessor transverse →
  sumRational (allCyclicIndices Side13.side13)
    (λ coordinate →
      sq (edgeDifferenceField field axis predecessor
        (insertAxis axis coordinate transverse)))
  ≡ thirteenℚ * sq (edgeDifferenceAtTransverse field axis predecessor transverse)
fibreMultiplicityThirteen field axis predecessor transverse =
  trans
    (sumRationalCong
      (allCyclicIndices Side13.side13)
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
        (allCyclicIndices Side13.side13)
        (sq (edgeDifferenceAtTransverse field axis predecessor transverse)))
      (lengthThirteen field axis predecessor transverse))
  where
  lengthThirteen : ∀ current currentAxis currentPredecessor currentTransverse →
    natAsRational (length (allCyclicIndices Side13.side13))
      * sq (edgeDifferenceAtTransverse
          current currentAxis currentPredecessor currentTransverse)
    ≡ thirteenℚ * sq (edgeDifferenceAtTransverse
          current currentAxis currentPredecessor currentTransverse)
  lengthThirteen current currentAxis currentPredecessor currentTransverse
    rewrite lengthAllCyclicIndices Side13.side13 = ℚRing.solve-∀

globalEdgeDifferenceNormThirteenfold : ∀ field axis predecessor →
  Norm.globalNormSq (edgeDifferenceField field axis predecessor)
  ≡ thirteenℚ * axisPredecessorEnergy axis field predecessor
globalEdgeDifferenceNormThirteenfold field axis predecessor =
  trans
    (sym (axisPartitionSumMatchesGlobal axis
      (λ site → sq (edgeDifferenceField field axis predecessor site))))
    (trans
      (sumRationalCong
        (physicalTransverseCoordinates Side13.side13)
        (λ transverse →
          sumRational (allCyclicIndices Side13.side13)
            (λ coordinate →
              sq (edgeDifferenceField field axis predecessor
                (insertAxis axis coordinate transverse))))
        (λ transverse →
          thirteenℚ * sq (edgeDifferenceAtTransverse
            field axis predecessor transverse))
        (fibreMultiplicityThirteen field axis predecessor))
      (sumRationalScale
        thirteenℚ
        (physicalTransverseCoordinates Side13.side13)
        (λ transverse →
          sq (edgeDifferenceAtTransverse field axis predecessor transverse))))

axisDirectionalEnergy : Axis4 → SiteField Side13.side13 → ℚ
axisDirectionalEnergy axis field =
  sumRational (physicalTransverseCoordinates Side13.side13)
    (physicalFibreEdgeEnergy field axis)

axisDirectionalEnergyAsPredecessorSum : ∀ axis field →
  axisDirectionalEnergy axis field
  ≡ sumRational (allCyclicIndices side12)
      (axisPredecessorEnergy axis field)
axisDirectionalEnergyAsPredecessorSum axis field =
  sumSwap
    (physicalTransverseCoordinates Side13.side13)
    (allCyclicIndices side12)
    (λ transverse predecessor →
      sq (edgeDifferenceAtTransverse field axis predecessor transverse))

sumRationalMonotone :
  ∀ {A : Set} (values : Agda.Builtin.List.List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  sumRational values left ≤ sumRational values right
sumRationalMonotone Agda.Builtin.List.[] left right pointwise = ℚP.≤-refl
sumRationalMonotone (Agda.Builtin.List._∷_ value values) left right pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumRationalMonotone values left right pointwise)

predecessorNormSumExact : ∀ field axis →
  sumRational (allCyclicIndices side12)
    (λ predecessor → Norm.globalNormSq (edgeDifferenceField field axis predecessor))
  ≡ thirteenℚ * axisDirectionalEnergy axis field
predecessorNormSumExact field axis =
  trans
    (sumRationalCong
      (allCyclicIndices side12)
      (λ predecessor → Norm.globalNormSq (edgeDifferenceField field axis predecessor))
      (λ predecessor → thirteenℚ * axisPredecessorEnergy axis field predecessor)
      (globalEdgeDifferenceNormThirteenfold field axis))
    (trans
      (sumRationalScale
        thirteenℚ
        (allCyclicIndices side12)
        (axisPredecessorEnergy axis field))
      (cong (thirteenℚ *_)
        (sym (axisDirectionalEnergyAsPredecessorSum axis field))))

thirteenTimesDirectionalEnergyContraction :
  ∀ averageAxis differenceAxis field →
  averageAxis ≢ differenceAxis →
  thirteenℚ * axisDirectionalEnergy differenceAxis
    (Average.axisAverage Side13.side13AverageData field averageAxis)
  ≤ thirteenℚ * axisDirectionalEnergy differenceAxis field
thirteenTimesDirectionalEnergyContraction averageAxis differenceAxis field distinct =
  subst
    (λ leftValue →
      leftValue ≤ thirteenℚ * axisDirectionalEnergy differenceAxis field)
    (predecessorNormSumExact
      (Average.axisAverage Side13.side13AverageData field averageAxis)
      differenceAxis)
    (subst
      (λ rightValue →
        sumRational (allCyclicIndices side12)
          (λ predecessor →
            Norm.globalNormSq
              (edgeDifferenceField
                (Average.axisAverage Side13.side13AverageData field averageAxis)
                differenceAxis predecessor))
        ≤ rightValue)
      (predecessorNormSumExact field differenceAxis)
      (sumRationalMonotone
        (allCyclicIndices side12)
        (λ predecessor →
          Norm.globalNormSq
            (edgeDifferenceField
              (Average.axisAverage Side13.side13AverageData field averageAxis)
              differenceAxis predecessor))
        (λ predecessor →
          Norm.globalNormSq (edgeDifferenceField field differenceAxis predecessor))
        (λ predecessor →
          fixedPredecessorNormContraction
            averageAxis differenceAxis field predecessor distinct)))

distinctAxisDirectionalEnergyContraction :
  ∀ averageAxis differenceAxis field →
  averageAxis ≢ differenceAxis →
  axisDirectionalEnergy differenceAxis
    (Average.axisAverage Side13.side13AverageData field averageAxis)
  ≤ axisDirectionalEnergy differenceAxis field
distinctAxisDirectionalEnergyContraction averageAxis differenceAxis field distinct =
  ℚP.*-cancelˡ-≤-pos thirteenℚ
    (thirteenTimesDirectionalEnergyContraction
      averageAxis differenceAxis field distinct)

path13DistinctAxisDirectionalEnergyContractionLevel : ProofLevel
path13DistinctAxisDirectionalEnergyContractionLevel = machineChecked
