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
open import Agda.Builtin.List using (List)
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
import DASHI.Physics.YangMills.BalabanFiniteSumRelationFibreLiftExact as SumLift
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
edgeDifferenceField fld axis predecessor site =
  fld (replaceAxis axis (sucᵢ predecessor) site)
  - fld (replaceAxis axis (weakenIndex predecessor) site)

axisAverageCommutesWithDistinctEdgeDifference :
  ∀ averageAxis differenceAxis fld predecessor site →
  averageAxis ≢ differenceAxis →
  edgeDifferenceField
    (Average.axisAverage Side13.side13AverageData fld averageAxis)
    differenceAxis predecessor site
  ≡ Average.axisAverage Side13.side13AverageData
      (edgeDifferenceField fld differenceAxis predecessor)
      averageAxis site
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ zeroᵢ fld predecessor site distinct = emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ zeroᵢ) fld predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) fld predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) fld predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) zeroᵢ fld predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) fld predecessor site distinct =
  emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) fld predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) fld predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ fld predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) fld predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct = ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ zeroᵢ))
  fld predecessor site distinct = emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  fld predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ
  fld predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ zeroᵢ)
  fld predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ (sucᵢ zeroᵢ))
  fld predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  ℚRing.solve-∀
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) fld predecessor site distinct =
  emptyElim (distinct refl)

edgeDifferenceAveragePointwise :
  ∀ averageAxis differenceAxis fld predecessor →
  averageAxis ≢ differenceAxis →
  Norm.FieldEqual
    (edgeDifferenceField
      (Average.axisAverage Side13.side13AverageData fld averageAxis)
      differenceAxis predecessor)
    (Average.axisAverage Side13.side13AverageData
      (edgeDifferenceField fld differenceAxis predecessor) averageAxis)
edgeDifferenceAveragePointwise averageAxis differenceAxis fld predecessor distinct site =
  axisAverageCommutesWithDistinctEdgeDifference
    averageAxis differenceAxis fld predecessor site distinct

fixedPredecessorNormContraction :
  ∀ averageAxis differenceAxis fld predecessor →
  averageAxis ≢ differenceAxis →
  Norm.globalNormSq
    (edgeDifferenceField
      (Average.axisAverage Side13.side13AverageData fld averageAxis)
      differenceAxis predecessor)
  ≤ Norm.globalNormSq (edgeDifferenceField fld differenceAxis predecessor)
fixedPredecessorNormContraction averageAxis differenceAxis fld predecessor distinct =
  subst
    (λ leftNorm →
      leftNorm ≤ Norm.globalNormSq (edgeDifferenceField fld differenceAxis predecessor))
    (sym (Norm.globalNormRespectsPointwise
      (edgeDifferenceAveragePointwise
        averageAxis differenceAxis fld predecessor distinct)))
    (Norm.axisAverageNormContraction Side13.side13AverageData
      (edgeDifferenceField fld differenceAxis predecessor) averageAxis)

edgeDifferenceAtTransverse :
  SiteField Side13.side13 → Axis4 → CyclicIndex side12 →
  Triple (CyclicIndex Side13.side13) → ℚ
edgeDifferenceAtTransverse fld axis predecessor transverse =
  fld (insertAxis axis (sucᵢ predecessor) transverse)
  - fld (insertAxis axis (weakenIndex predecessor) transverse)

edgeDifferenceOnInsertedAxis :
  ∀ fld axis predecessor coordinate transverse →
  edgeDifferenceField fld axis predecessor
    (insertAxis axis coordinate transverse)
  ≡ edgeDifferenceAtTransverse fld axis predecessor transverse
edgeDifferenceOnInsertedAxis fld axis predecessor coordinate transverse
  rewrite extractInsertTransverse axis coordinate transverse = refl

axisPredecessorEnergy :
  Axis4 → SiteField Side13.side13 → CyclicIndex side12 → ℚ
axisPredecessorEnergy axis fld predecessor =
  sumRational (physicalTransverseCoordinates Side13.side13)
    (λ transverse → sq (edgeDifferenceAtTransverse fld axis predecessor transverse))

fibreMultiplicityThirteen : ∀ fld axis predecessor transverse →
  sumRational (allCyclicIndices Side13.side13)
    (λ coordinate →
      sq (edgeDifferenceField fld axis predecessor
        (insertAxis axis coordinate transverse)))
  ≡ thirteenℚ * sq (edgeDifferenceAtTransverse fld axis predecessor transverse)
fibreMultiplicityThirteen fld axis predecessor transverse =
  trans
    (sumRationalCong
      (allCyclicIndices Side13.side13)
      (λ coordinate →
        sq (edgeDifferenceField fld axis predecessor
          (insertAxis axis coordinate transverse)))
      (λ coordinate →
        sq (edgeDifferenceAtTransverse fld axis predecessor transverse))
      (λ coordinate →
        cong sq (edgeDifferenceOnInsertedAxis
          fld axis predecessor coordinate transverse)))
    (trans
      (sumRationalConstant
        (allCyclicIndices Side13.side13)
        (sq (edgeDifferenceAtTransverse fld axis predecessor transverse)))
      (lengthThirteen fld axis predecessor transverse))
  where
  lengthThirteen : ∀ current currentAxis currentPredecessor currentTransverse →
    natAsRational (length (allCyclicIndices Side13.side13))
      * sq (edgeDifferenceAtTransverse
          current currentAxis currentPredecessor currentTransverse)
    ≡ thirteenℚ * sq (edgeDifferenceAtTransverse
          current currentAxis currentPredecessor currentTransverse)
  lengthThirteen current currentAxis currentPredecessor currentTransverse
    rewrite lengthAllCyclicIndices Side13.side13 = ℚRing.solve-∀

globalEdgeDifferenceNormThirteenfold : ∀ fld axis predecessor →
  Norm.globalNormSq (edgeDifferenceField fld axis predecessor)
  ≡ thirteenℚ * axisPredecessorEnergy axis fld predecessor
globalEdgeDifferenceNormThirteenfold fld axis predecessor =
  trans
    (sym (axisPartitionSumMatchesGlobal axis
      (λ site → sq (edgeDifferenceField fld axis predecessor site))))
    (trans
      (sumRationalCong
        (physicalTransverseCoordinates Side13.side13)
        (λ transverse →
          sumRational (allCyclicIndices Side13.side13)
            (λ coordinate →
              sq (edgeDifferenceField fld axis predecessor
                (insertAxis axis coordinate transverse))))
        (λ transverse →
          thirteenℚ * sq (edgeDifferenceAtTransverse
            fld axis predecessor transverse))
        (fibreMultiplicityThirteen fld axis predecessor))
      (sumRationalScale
        thirteenℚ
        (physicalTransverseCoordinates Side13.side13)
        (λ transverse →
          sq (edgeDifferenceAtTransverse fld axis predecessor transverse))))

axisDirectionalEnergy : Axis4 → SiteField Side13.side13 → ℚ
axisDirectionalEnergy axis fld =
  sumRational (physicalTransverseCoordinates Side13.side13)
    (physicalFibreEdgeEnergy fld axis)

axisDirectionalEnergyAsPredecessorSum : ∀ axis fld →
  axisDirectionalEnergy axis fld
  ≡ sumRational (allCyclicIndices side12)
      (axisPredecessorEnergy axis fld)
axisDirectionalEnergyAsPredecessorSum axis fld =
  sumSwap
    (physicalTransverseCoordinates Side13.side13)
    (allCyclicIndices side12)
    (λ transverse predecessor →
      sq (edgeDifferenceAtTransverse fld axis predecessor transverse))

-- Compatibility name retained for downstream users; the aggregate inequality
-- is supplied by the canonical relation-preserving finite-sum fibre observer.
sumRationalMonotone :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  sumRational values left ≤ sumRational values right
sumRationalMonotone = SumLift.sumRationalMonotoneViaFibre

predecessorNormSumExact : ∀ fld axis →
  sumRational (allCyclicIndices side12)
    (λ predecessor → Norm.globalNormSq (edgeDifferenceField fld axis predecessor))
  ≡ thirteenℚ * axisDirectionalEnergy axis fld
predecessorNormSumExact fld axis =
  trans
    (sumRationalCong
      (allCyclicIndices side12)
      (λ predecessor → Norm.globalNormSq (edgeDifferenceField fld axis predecessor))
      (λ predecessor → thirteenℚ * axisPredecessorEnergy axis fld predecessor)
      (globalEdgeDifferenceNormThirteenfold fld axis))
    (trans
      (sumRationalScale
        thirteenℚ
        (allCyclicIndices side12)
        (axisPredecessorEnergy axis fld))
      (cong (thirteenℚ *_)
        (sym (axisDirectionalEnergyAsPredecessorSum axis fld))))

thirteenTimesDirectionalEnergyContraction :
  ∀ averageAxis differenceAxis fld →
  averageAxis ≢ differenceAxis →
  thirteenℚ * axisDirectionalEnergy differenceAxis
    (Average.axisAverage Side13.side13AverageData fld averageAxis)
  ≤ thirteenℚ * axisDirectionalEnergy differenceAxis fld
thirteenTimesDirectionalEnergyContraction averageAxis differenceAxis fld distinct =
  subst
    (λ leftValue →
      leftValue ≤ thirteenℚ * axisDirectionalEnergy differenceAxis fld)
    (predecessorNormSumExact
      (Average.axisAverage Side13.side13AverageData fld averageAxis)
      differenceAxis)
    (subst
      (λ rightValue →
        sumRational (allCyclicIndices side12)
          (λ predecessor →
            Norm.globalNormSq
              (edgeDifferenceField
                (Average.axisAverage Side13.side13AverageData fld averageAxis)
                differenceAxis predecessor))
        ≤ rightValue)
      (predecessorNormSumExact fld differenceAxis)
      (sumRationalMonotone
        (allCyclicIndices side12)
        (λ predecessor →
          Norm.globalNormSq
            (edgeDifferenceField
              (Average.axisAverage Side13.side13AverageData fld averageAxis)
              differenceAxis predecessor))
        (λ predecessor →
          Norm.globalNormSq (edgeDifferenceField fld differenceAxis predecessor))
        (λ predecessor →
          fixedPredecessorNormContraction
            averageAxis differenceAxis fld predecessor distinct)))

distinctAxisDirectionalEnergyContraction :
  ∀ averageAxis differenceAxis fld →
  averageAxis ≢ differenceAxis →
  axisDirectionalEnergy differenceAxis
    (Average.axisAverage Side13.side13AverageData fld averageAxis)
  ≤ axisDirectionalEnergy differenceAxis fld
distinctAxisDirectionalEnergyContraction averageAxis differenceAxis fld distinct =
  ℚP.*-cancelˡ-≤-pos thirteenℚ
    (thirteenTimesDirectionalEnergyContraction
      averageAxis differenceAxis fld distinct)

path13DistinctAxisDirectionalEnergyContractionLevel : ProofLevel
path13DistinctAxisDirectionalEnergyContractionLevel = machineChecked
