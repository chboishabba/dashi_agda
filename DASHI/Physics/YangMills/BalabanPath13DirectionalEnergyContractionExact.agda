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
import DASHI.Physics.YangMills.BalabanOpaqueGlobalAlgebraExact as OpaqueAlgebra
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
edgeDifferenceField siteField axis predecessor site =
  siteField (replaceAxis axis (sucᵢ predecessor) site)
  - siteField (replaceAxis axis (weakenIndex predecessor) site)

scaleSumSubtractCommutes :
  ∀ {A : Set} (values : List A) (scale : ℚ) (f g : A → ℚ) →
  scale * sumRational values f - scale * sumRational values g
  ≡ scale * sumRational values (λ x → f x - g x)
scaleSumSubtractCommutes values scale f g =
  trans
    (OpaqueAlgebra.scaleSubFactor scale (sumRational values f) (sumRational values g))
    (cong (scale *_) (sym (Average.sumRationalSubtract values f g)))

commuteStep :
  ∀ siteField diffAxis pred avgAxis site →
  Average.weight Side13.side13AverageData
    * sumRational (allCyclicIndices Side13.side13)
        (λ c → siteField (replaceAxis diffAxis (sucᵢ pred) (insertAxis avgAxis c (axisTransverse avgAxis site))))
  - Average.weight Side13.side13AverageData
    * sumRational (allCyclicIndices Side13.side13)
        (λ c → siteField (replaceAxis diffAxis (weakenIndex pred) (insertAxis avgAxis c (axisTransverse avgAxis site))))
  ≡ Average.axisAverage Side13.side13AverageData
      (edgeDifferenceField siteField diffAxis pred)
      avgAxis site
commuteStep siteField diffAxis pred avgAxis site =
  scaleSumSubtractCommutes (allCyclicIndices Side13.side13)
    (Average.weight Side13.side13AverageData)
    (λ c → siteField (replaceAxis diffAxis (sucᵢ pred) (insertAxis avgAxis c (axisTransverse avgAxis site))))
    (λ c → siteField (replaceAxis diffAxis (weakenIndex pred) (insertAxis avgAxis c (axisTransverse avgAxis site))))

axisAverageCommutesWithDistinctEdgeDifference :
  ∀ averageAxis differenceAxis siteField predecessor site →
  averageAxis ≢ differenceAxis →
  edgeDifferenceField
    (Average.axisAverage Side13.side13AverageData siteField averageAxis)
    differenceAxis predecessor site
  ≡ Average.axisAverage Side13.side13AverageData
      (edgeDifferenceField siteField differenceAxis predecessor)
      averageAxis site
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ zeroᵢ siteField predecessor site distinct = emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ zeroᵢ) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField (sucᵢ zeroᵢ) predecessor zeroᵢ (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField (sucᵢ (sucᵢ zeroᵢ)) predecessor zeroᵢ (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) predecessor zeroᵢ (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) zeroᵢ siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField zeroᵢ predecessor (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) siteField predecessor site distinct =
  emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField (sucᵢ (sucᵢ zeroᵢ)) predecessor (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) predecessor (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField zeroᵢ predecessor (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) siteField predecessor
  (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField (sucᵢ zeroᵢ) predecessor (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ zeroᵢ))
  siteField predecessor site distinct = emptyElim (distinct refl)
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  siteField predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) predecessor (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ
  siteField predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField zeroᵢ predecessor (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ zeroᵢ)
  siteField predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField (sucᵢ zeroᵢ) predecessor (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ (sucᵢ zeroᵢ))
  siteField predecessor (pair (pair x0 x1) (pair x2 x3)) distinct =
  commuteStep siteField (sucᵢ (sucᵢ zeroᵢ)) predecessor (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3))
axisAverageCommutesWithDistinctEdgeDifference
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField predecessor site distinct =
  emptyElim (distinct refl)

edgeDifferenceAveragePointwise :
  ∀ averageAxis differenceAxis siteField predecessor →
  averageAxis ≢ differenceAxis →
  Norm.FieldEqual
    (edgeDifferenceField
      (Average.axisAverage Side13.side13AverageData siteField averageAxis)
      differenceAxis predecessor)
    (Average.axisAverage Side13.side13AverageData
      (edgeDifferenceField siteField differenceAxis predecessor) averageAxis)
edgeDifferenceAveragePointwise averageAxis differenceAxis siteField predecessor distinct site =
  axisAverageCommutesWithDistinctEdgeDifference
    averageAxis differenceAxis siteField predecessor site distinct

fixedPredecessorNormContraction :
  ∀ averageAxis differenceAxis siteField predecessor →
  averageAxis ≢ differenceAxis →
  Norm.globalNormSq
    (edgeDifferenceField
      (Average.axisAverage Side13.side13AverageData siteField averageAxis)
      differenceAxis predecessor)
  ≤ Norm.globalNormSq (edgeDifferenceField siteField differenceAxis predecessor)
fixedPredecessorNormContraction averageAxis differenceAxis siteField predecessor distinct =
  subst
    (λ leftNorm →
      leftNorm ≤ Norm.globalNormSq (edgeDifferenceField siteField differenceAxis predecessor))
    (sym (Norm.globalNormRespectsPointwise
      (edgeDifferenceAveragePointwise
        averageAxis differenceAxis siteField predecessor distinct)))
    (Norm.axisAverageNormContraction Side13.side13AverageData
      (edgeDifferenceField siteField differenceAxis predecessor) averageAxis)

edgeDifferenceAtTransverse :
  SiteField Side13.side13 → Axis4 → CyclicIndex side12 →
  Triple (CyclicIndex Side13.side13) → ℚ
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
  Axis4 → SiteField Side13.side13 → CyclicIndex side12 → ℚ
axisPredecessorEnergy axis siteField predecessor =
  sumRational (physicalTransverseCoordinates Side13.side13)
    (λ transverse → sq (edgeDifferenceAtTransverse siteField axis predecessor transverse))

fibreMultiplicityThirteen : ∀ siteField axis predecessor transverse →
  sumRational (allCyclicIndices Side13.side13)
    (λ coordinate →
      sq (edgeDifferenceField siteField axis predecessor
        (insertAxis axis coordinate transverse)))
  ≡ thirteenℚ * sq (edgeDifferenceAtTransverse siteField axis predecessor transverse)
fibreMultiplicityThirteen siteField axis predecessor transverse =
  trans
    (sumRationalCong
      (allCyclicIndices Side13.side13)
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
        (allCyclicIndices Side13.side13)
        (sq (edgeDifferenceAtTransverse siteField axis predecessor transverse)))
      (lengthThirteen siteField axis predecessor transverse))
  where
  lengthThirteen : ∀ current currentAxis currentPredecessor currentTransverse →
    natAsRational (length (allCyclicIndices Side13.side13))
      * sq (edgeDifferenceAtTransverse
          current currentAxis currentPredecessor currentTransverse)
    ≡ thirteenℚ * sq (edgeDifferenceAtTransverse
          current currentAxis currentPredecessor currentTransverse)
  lengthThirteen current currentAxis currentPredecessor currentTransverse
    rewrite lengthAllCyclicIndices Side13.side13 = refl

globalEdgeDifferenceNormThirteenfold : ∀ siteField axis predecessor →
  Norm.globalNormSq (edgeDifferenceField siteField axis predecessor)
  ≡ thirteenℚ * axisPredecessorEnergy axis siteField predecessor
globalEdgeDifferenceNormThirteenfold siteField axis predecessor =
  trans
    (sym (axisPartitionSumMatchesGlobal axis
      (λ site → sq (edgeDifferenceField siteField axis predecessor site))))
    (trans
      (sumRationalCong
        (physicalTransverseCoordinates Side13.side13)
        (λ transverse →
          sumRational (allCyclicIndices Side13.side13)
            (λ coordinate →
              sq (edgeDifferenceField siteField axis predecessor
                (insertAxis axis coordinate transverse))))
        (λ transverse →
          thirteenℚ * sq (edgeDifferenceAtTransverse
            siteField axis predecessor transverse))
        (fibreMultiplicityThirteen siteField axis predecessor))
      (sumRationalScale
        thirteenℚ
        (physicalTransverseCoordinates Side13.side13)
        (λ transverse →
          sq (edgeDifferenceAtTransverse siteField axis predecessor transverse))))

axisDirectionalEnergy : Axis4 → SiteField Side13.side13 → ℚ
axisDirectionalEnergy axis siteField =
  sumRational (physicalTransverseCoordinates Side13.side13)
    (physicalFibreEdgeEnergy siteField axis)

axisDirectionalEnergyAsPredecessorSum : ∀ axis siteField →
  axisDirectionalEnergy axis siteField
  ≡ sumRational (allCyclicIndices side12)
      (axisPredecessorEnergy axis siteField)
axisDirectionalEnergyAsPredecessorSum axis siteField =
  sumSwap
    (physicalTransverseCoordinates Side13.side13)
    (allCyclicIndices side12)
    (λ transverse predecessor →
      sq (edgeDifferenceAtTransverse siteField axis predecessor transverse))

-- Compatibility name retained for downstream users; the aggregate inequality
-- is supplied by the canonical relation-preserving finite-sum fibre observer.
sumRationalMonotone :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  sumRational values left ≤ sumRational values right
sumRationalMonotone = SumLift.sumRationalMonotoneViaFibre

predecessorNormSumExact : ∀ siteField axis →
  sumRational (allCyclicIndices side12)
    (λ predecessor → Norm.globalNormSq (edgeDifferenceField siteField axis predecessor))
  ≡ thirteenℚ * axisDirectionalEnergy axis siteField
predecessorNormSumExact siteField axis =
  trans
    (sumRationalCong
      (allCyclicIndices side12)
      (λ predecessor → Norm.globalNormSq (edgeDifferenceField siteField axis predecessor))
      (λ predecessor → thirteenℚ * axisPredecessorEnergy axis siteField predecessor)
      (globalEdgeDifferenceNormThirteenfold siteField axis))
    (trans
      (sumRationalScale
        thirteenℚ
        (allCyclicIndices side12)
        (axisPredecessorEnergy axis siteField))
      (cong (thirteenℚ *_)
        (sym (axisDirectionalEnergyAsPredecessorSum axis siteField))))

thirteenTimesDirectionalEnergyContraction :
  ∀ averageAxis differenceAxis siteField →
  averageAxis ≢ differenceAxis →
  thirteenℚ * axisDirectionalEnergy differenceAxis
    (Average.axisAverage Side13.side13AverageData siteField averageAxis)
  ≤ thirteenℚ * axisDirectionalEnergy differenceAxis siteField
thirteenTimesDirectionalEnergyContraction averageAxis differenceAxis siteField distinct =
  subst
    (λ leftValue →
      leftValue ≤ thirteenℚ * axisDirectionalEnergy differenceAxis siteField)
    (predecessorNormSumExact
      (Average.axisAverage Side13.side13AverageData siteField averageAxis)
      differenceAxis)
    (subst
      (λ rightValue →
        sumRational (allCyclicIndices side12)
          (λ predecessor →
            Norm.globalNormSq
              (edgeDifferenceField
                (Average.axisAverage Side13.side13AverageData siteField averageAxis)
                differenceAxis predecessor))
        ≤ rightValue)
      (predecessorNormSumExact siteField differenceAxis)
      (sumRationalMonotone
        (allCyclicIndices side12)
        (λ predecessor →
          Norm.globalNormSq
            (edgeDifferenceField
              (Average.axisAverage Side13.side13AverageData siteField averageAxis)
              differenceAxis predecessor))
        (λ predecessor →
          Norm.globalNormSq (edgeDifferenceField siteField differenceAxis predecessor))
        (λ predecessor →
          fixedPredecessorNormContraction
            averageAxis differenceAxis siteField predecessor distinct)))

distinctAxisDirectionalEnergyContraction :
  ∀ averageAxis differenceAxis siteField →
  averageAxis ≢ differenceAxis →
  axisDirectionalEnergy differenceAxis
    (Average.axisAverage Side13.side13AverageData siteField averageAxis)
  ≤ axisDirectionalEnergy differenceAxis siteField
distinctAxisDirectionalEnergyContraction averageAxis differenceAxis siteField distinct =
  ℚP.*-cancelˡ-≤-pos thirteenℚ
    (thirteenTimesDirectionalEnergyContraction
      averageAxis differenceAxis siteField distinct)

path13DistinctAxisDirectionalEnergyContractionLevel : ProofLevel
path13DistinctAxisDirectionalEnergyContractionLevel = machineChecked
