module DASHI.Physics.YangMills.BalabanNormalizedAxisAverageExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- P. K. Mitter, "The Exact Renormalization Group",
-- arXiv:math-ph/0505008. No DOI recorded for the cited encyclopedia preprint.
--
-- DASHI CONTRIBUTION
--
-- Remove the accidental side-four specialization from the finite conditional
-- expectation calculus.  A normalized physical axis average is now defined
-- for any finite side L and any rational weight w satisfying
--
--       w * |CyclicIndex L| = 1.
--
-- From that single normalization proof we derive, on the literal L^4 carrier:
-- idempotence, zero-sum centering, pairwise commutation of all four coordinate
-- expectations, and self-adjointness in the global finite L2 inner product.
-- These are exactly the structural ingredients needed to migrate the Gate-I
-- martingale/Poincare machinery from the side-four test carrier to L=13.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact as Partition

record NormalizedAxisAverageData (L : Nat) : Set where
  field
    weight : ℚ
    normalized :
      weight * natAsRational (length (allCyclicIndices L)) ≡ 1ℚ

open NormalizedAxisAverageData public

axisAverage :
  ∀ {L} → NormalizedAxisAverageData L →
  SiteField L → Axis4 → SiteField L
axisAverage dataSet siteF axis site =
  weight dataSet * physicalFibreSum siteF axis (axisTransverse axis site)

axisCentering :
  ∀ {L} → NormalizedAxisAverageData L →
  SiteField L → Axis4 → SiteField L
axisCentering dataSet siteF axis site =
  siteF site - axisAverage dataSet siteF axis site

axisAverageConstantOnFibre :
  ∀ {L} (dataSet : NormalizedAxisAverageData L)
    siteF axis transverse coordinate →
  axisAverage dataSet siteF axis (insertAxis axis coordinate transverse)
  ≡ weight dataSet * physicalFibreSum siteF axis transverse
axisAverageConstantOnFibre dataSet siteF axis transverse coordinate
  rewrite extractInsertTransverse axis coordinate transverse = refl

normalizedAverageOfConstant :
  ∀ {L} (dataSet : NormalizedAxisAverageData L) value →
  weight dataSet
    * sumRational (allCyclicIndices L) (λ _ → value)
  ≡ value
normalizedAverageOfConstant {L} dataSet value =
  trans
    (cong (weight dataSet *_)
      (sumRationalConstant (allCyclicIndices L) value))
    (trans
      (ℚP.*-assoc
        (weight dataSet)
        (natAsRational (length (allCyclicIndices L))) value)
      (trans
        (cong (_* value) (normalized dataSet))
        (ℚP.*-identityˡ value)))

coefficientDoubleSumSwap :
  ∀ coefficient {A B : Set} (left : List A) (right : List B)
    (term : A → B → ℚ) →
  coefficient * sumRational left
    (λ leftValue → coefficient * sumRational right (term leftValue))
  ≡ coefficient * sumRational right
    (λ rightValue → coefficient * sumRational left
      (λ leftValue → term leftValue rightValue))
coefficientDoubleSumSwap coefficient left right term =
  trans
    (cong (coefficient *_)
      (sumRationalScale coefficient left
        (λ leftValue → sumRational right (term leftValue))))
    (trans
      (cong (λ value → coefficient * (coefficient * value))
        (sumSwap left right term))
      (cong (coefficient *_)
        (sym
          (sumRationalScale coefficient right
            (λ rightValue →
              sumRational left (λ leftValue → term leftValue rightValue))))))

axisAverageIdempotent :
  ∀ {L} (dataSet : NormalizedAxisAverageData L) siteF axis site →
  axisAverage dataSet (axisAverage dataSet siteF axis) axis site
  ≡ axisAverage dataSet siteF axis site
axisAverageIdempotent {L} dataSet siteF axis site =
  trans
    (cong (weight dataSet *_)
      (sumRationalCong
        (allCyclicIndices L)
        (λ coordinate →
          axisAverage dataSet siteF axis
            (insertAxis axis coordinate (axisTransverse axis site)))
        (λ _ →
          weight dataSet
            * physicalFibreSum siteF axis (axisTransverse axis site))
        (λ coordinate →
          axisAverageConstantOnFibre dataSet
            siteF axis (axisTransverse axis site) coordinate)))
    (normalizedAverageOfConstant dataSet
      (weight dataSet
        * physicalFibreSum siteF axis (axisTransverse axis site)))

axisAverageCommutes :
  ∀ {L} (dataSet : NormalizedAxisAverageData L)
    left right siteF site →
  axisAverage dataSet (axisAverage dataSet siteF left) right site
  ≡ axisAverage dataSet (axisAverage dataSet siteF right) left site
axisAverageCommutes {L} dataSet zeroᵢ zeroᵢ siteF site = refl
axisAverageCommutes {L} dataSet zeroᵢ (sucᵢ zeroᵢ) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair fixed moving) (pair x2 x3)))
axisAverageCommutes {L} dataSet zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair fixed x1) (pair moving x3)))
axisAverageCommutes {L} dataSet zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair fixed x1) (pair x2 moving)))
axisAverageCommutes {L} dataSet (sucᵢ zeroᵢ) zeroᵢ siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair moving fixed) (pair x2 x3)))
axisAverageCommutes {L} dataSet (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) siteF site = refl
axisAverageCommutes {L} dataSet (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair x0 fixed) (pair moving x3)))
axisAverageCommutes {L} dataSet (sucᵢ zeroᵢ)
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair x0 fixed) (pair x2 moving)))
axisAverageCommutes {L} dataSet (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair moving x1) (pair fixed x3)))
axisAverageCommutes {L} dataSet (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair x0 moving) (pair fixed x3)))
axisAverageCommutes {L} dataSet (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ zeroᵢ)) siteF site = refl
axisAverageCommutes {L} dataSet (sucᵢ (sucᵢ zeroᵢ))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair x0 x1) (pair fixed moving)))
axisAverageCommutes {L} dataSet (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ siteF
  (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair moving x1) (pair x2 fixed)))
axisAverageCommutes {L} dataSet (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ zeroᵢ) siteF (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair x0 moving) (pair x2 fixed)))
axisAverageCommutes {L} dataSet (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ zeroᵢ)) siteF (pair (pair x0 x1) (pair x2 x3)) =
  coefficientDoubleSumSwap (weight dataSet)
    (allCyclicIndices L) (allCyclicIndices L)
    (λ moving fixed → siteF (pair (pair x0 x1) (pair moving fixed)))
axisAverageCommutes {L} dataSet (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteF site = refl

sumRationalSubtract :
  ∀ {A : Set} values (left right : A → ℚ) →
  sumRational values (λ value → left value - right value)
  ≡ sumRational values left - sumRational values right
sumRationalSubtract [] left right = ℚRing.solve-∀
sumRationalSubtract (value ∷ values) left right
  rewrite sumRationalSubtract values left right = ℚRing.solve-∀

axisCenteringFibreSumZero :
  ∀ {L} (dataSet : NormalizedAxisAverageData L)
    siteF axis transverse →
  sumRational (allCyclicIndices L)
    (λ coordinate →
      axisCentering dataSet siteF axis
        (insertAxis axis coordinate transverse))
  ≡ 0ℚ
axisCenteringFibreSumZero {L} dataSet siteF axis transverse =
  let
    averageValue = weight dataSet * physicalFibreSum siteF axis transverse
    centeredPointwise : ∀ coordinate →
      axisCentering dataSet siteF axis
        (insertAxis axis coordinate transverse)
      ≡ siteF (insertAxis axis coordinate transverse) - averageValue
    centeredPointwise coordinate =
      cong
        (λ avg → siteF (insertAxis axis coordinate transverse) - avg)
        (axisAverageConstantOnFibre dataSet siteF axis transverse coordinate)

    sumToDifference :
      sumRational (allCyclicIndices L)
        (λ coordinate →
          siteF (insertAxis axis coordinate transverse) - averageValue)
      ≡ physicalFibreSum siteF axis transverse
        - sumRational (allCyclicIndices L) (λ _ → averageValue)
    sumToDifference = sumRationalSubtract
      (allCyclicIndices L)
      (λ coordinate → siteF (insertAxis axis coordinate transverse))
      (λ _ → averageValue)
  in
  trans
    (sumRationalCong
      (allCyclicIndices L)
      (λ coordinate →
        axisCentering dataSet siteF axis
          (insertAxis axis coordinate transverse))
      (λ coordinate →
        siteF (insertAxis axis coordinate transverse) - averageValue)
      centeredPointwise)
    (trans sumToDifference
      (trans
        (cong
          (λ averagedTotal →
            physicalFibreSum siteF axis transverse - averagedTotal)
          (sym
            (normalizedAverageOfConstant dataSet
              (physicalFibreSum siteF axis transverse))))
        (ℚRing.solve-∀)))

------------------------------------------------------------------------
-- Self-adjointness in the literal global block inner product.
------------------------------------------------------------------------

toAxisFibreField :
  ∀ {L} → Axis4 → SiteField L →
  FibreField (Triple (CyclicIndex L)) (CyclicIndex L)
toAxisFibreField axis siteField transverse coordinate =
  siteField (insertAxis axis coordinate transverse)

axisAverageProjectionMatchesPhysical :
  ∀ {L} (dataSet : NormalizedAxisAverageData L)
    (axis : Axis4) (siteField : SiteField L)
    (transverse : Triple (CyclicIndex L))
    (coordinate : CyclicIndex L) →
  fibreAverageProjection (weight dataSet) (allCyclicIndices L)
    (toAxisFibreField axis siteField) transverse coordinate
  ≡ axisAverage dataSet siteField axis
      (insertAxis axis coordinate transverse)
axisAverageProjectionMatchesPhysical dataSet axis siteField transverse coordinate =
  sym (axisAverageConstantOnFibre dataSet siteField axis transverse coordinate)

partitionAverageLeftMatchesProductInner :
  ∀ {L} (dataSet : NormalizedAxisAverageData L)
    (axis : Axis4) (left right : SiteField L) →
  Partition.axisPartitionInner axis (axisAverage dataSet left axis) right
  ≡ productInner
      (physicalTransverseCoordinates L)
      (allCyclicIndices L)
      (fibreAverageProjection (weight dataSet) (allCyclicIndices L)
        (toAxisFibreField axis left))
      (toAxisFibreField axis right)
partitionAverageLeftMatchesProductInner {L} dataSet axis left right =
  sumRationalCong
    (physicalTransverseCoordinates L) _ _ (λ transverse →
      sumRationalCong (allCyclicIndices L) _ _ (λ coordinate →
        cong
          (λ x → x * right (insertAxis axis coordinate transverse))
          (sym (axisAverageProjectionMatchesPhysical
            dataSet axis left transverse coordinate))))

partitionAverageRightMatchesProductInner :
  ∀ {L} (dataSet : NormalizedAxisAverageData L)
    (axis : Axis4) (left right : SiteField L) →
  Partition.axisPartitionInner axis left (axisAverage dataSet right axis)
  ≡ productInner
      (physicalTransverseCoordinates L)
      (allCyclicIndices L)
      (toAxisFibreField axis left)
      (fibreAverageProjection (weight dataSet) (allCyclicIndices L)
        (toAxisFibreField axis right))
partitionAverageRightMatchesProductInner {L} dataSet axis left right =
  sumRationalCong
    (physicalTransverseCoordinates L) _ _ (λ transverse →
      sumRationalCong (allCyclicIndices L) _ _ (λ coordinate →
        cong
          (λ x → left (insertAxis axis coordinate transverse) * x)
          (sym (axisAverageProjectionMatchesPhysical
            dataSet axis right transverse coordinate))))

axisAverageSelfAdjoint :
  ∀ {L} (dataSet : NormalizedAxisAverageData L)
    (axis : Axis4) (left right : SiteField L) →
  Partition.globalBlockInner (axisAverage dataSet left axis) right
  ≡ Partition.globalBlockInner left (axisAverage dataSet right axis)
axisAverageSelfAdjoint {L} dataSet axis left right =
  trans
    (sym (Partition.axisPartitionInnerMatchesGlobal axis
      (axisAverage dataSet left axis) right))
    (trans
      (partitionAverageLeftMatchesProductInner dataSet axis left right)
      (trans
        (finiteFibreAverageSelfAdjoint
          (weight dataSet)
          (physicalTransverseCoordinates L)
          (allCyclicIndices L)
          (toAxisFibreField axis left)
          (toAxisFibreField axis right))
        (trans
          (sym (partitionAverageRightMatchesProductInner
            dataSet axis left right))
          (Partition.axisPartitionInnerMatchesGlobal axis
            left (axisAverage dataSet right axis)))))

normalizedAxisAverageIdempotenceLevel : ProofLevel
normalizedAxisAverageIdempotenceLevel = machineChecked

normalizedAxisAverageCommutationLevel : ProofLevel
normalizedAxisAverageCommutationLevel = machineChecked

normalizedAxisCenteringMeanZeroLevel : ProofLevel
normalizedAxisCenteringMeanZeroLevel = machineChecked

normalizedAxisAverageSelfAdjointnessLevel : ProofLevel
normalizedAxisAverageSelfAdjointnessLevel = machineChecked
