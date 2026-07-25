module DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
open import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact

------------------------------------------------------------------------
-- The literal block sum is independent of which coordinate is presented as
-- the fibre coordinate.  This is the missing physical Fubini bridge between
-- the axis-fibre proofs and the repository's one global block inner product.
------------------------------------------------------------------------

axisValues : (L : Nat) → Agda.Builtin.List.List (CyclicIndex L)
axisValues = allCyclicIndices

pairValues : (L : Nat) → Agda.Builtin.List.List (Pair2 (CyclicIndex L))
pairValues L = cartesian (axisValues L) (axisValues L)

coordinateSum4 : ∀ {L} → SiteField L → ℚ
coordinateSum4 {L} siteField =
  sum4
    (axisValues L) (axisValues L) (axisValues L) (axisValues L)
    (λ x0 x1 x2 x3 → siteField (pair (pair x0 x1) (pair x2 x3)))

globalSiteSum : ∀ {L} → SiteField L → ℚ
globalSiteSum {L} siteField = sumRational (physicalBlockSites L) siteField

globalSiteSumMatchesCoordinateSum4 : ∀ {L} siteField →
  globalSiteSum {L} siteField ≡ coordinateSum4 siteField
globalSiteSumMatchesCoordinateSum4 {L} siteField =
  trans
    (sumCartesian (pairValues L) (pairValues L) siteField)
    (trans
      (sumCartesian
        (axisValues L) (axisValues L)
        (λ pair01 →
          sumRational (pairValues L)
            (λ pair23 → siteField (pair pair01 pair23))))
      (sumRationalCong
        (axisValues L)
        (λ x0 →
          sumRational (axisValues L) (λ x1 →
            sumRational (pairValues L) (λ pair23 →
              siteField (pair (pair x0 x1) pair23))))
        (λ x0 →
          sumRational (axisValues L) (λ x1 →
            sumRational (axisValues L) (λ x2 →
              sumRational (axisValues L) (λ x3 →
                siteField (pair (pair x0 x1) (pair x2 x3))))))
        (λ x0 →
          sumRationalCong
            (axisValues L)
            (λ x1 →
              sumRational (pairValues L) (λ pair23 →
                siteField (pair (pair x0 x1) pair23)))
            (λ x1 →
              sumRational (axisValues L) (λ x2 →
                sumRational (axisValues L) (λ x3 →
                  siteField (pair (pair x0 x1) (pair x2 x3)))))
            (λ x1 →
              sumCartesian
                (axisValues L) (axisValues L)
                (λ pair23 → siteField (pair (pair x0 x1) pair23))))))

axisPartitionSum : ∀ {L} → Axis4 → SiteField L → ℚ
axisPartitionSum {L} axis siteField =
  sumRational (physicalTransverseCoordinates L) (λ transverse →
    sumRational (axisValues L) (λ coordinate →
      siteField (insertAxis axis coordinate transverse)))

axis0PartitionMatchesCoordinateSum4 : ∀ {L} siteField →
  axisPartitionSum zeroᵢ siteField ≡ coordinateSum4 siteField
axis0PartitionMatchesCoordinateSum4 {L} siteField =
  trans
    (sumCartesian
      (axisValues L) (pairValues L)
      (λ transverse →
        sumRational (axisValues L) (λ coordinate →
          siteField (insertAxis zeroᵢ coordinate transverse))))
    (trans
      (sumRationalCong
        (axisValues L)
        (λ x1 →
          sumRational (pairValues L) (λ pair23 →
            sumRational (axisValues L) (λ x0 →
              siteField (pair (pair x0 x1) pair23))))
        (λ x1 →
          sumRational (axisValues L) (λ x2 →
            sumRational (axisValues L) (λ x3 →
              sumRational (axisValues L) (λ x0 →
                siteField (pair (pair x0 x1) (pair x2 x3))))))
        (λ x1 →
          sumCartesian
            (axisValues L) (axisValues L)
            (λ pair23 →
              sumRational (axisValues L) (λ x0 →
                siteField (pair (pair x0 x1) pair23)))))
      (rotateAxis0ToCanonical
        (axisValues L) (axisValues L) (axisValues L) (axisValues L)
        (λ x0 x1 x2 x3 → siteField (pair (pair x0 x1) (pair x2 x3)))))

axis1PartitionMatchesCoordinateSum4 : ∀ {L} siteField →
  axisPartitionSum (sucᵢ zeroᵢ) siteField ≡ coordinateSum4 siteField
axis1PartitionMatchesCoordinateSum4 {L} siteField =
  trans
    (sumCartesian
      (axisValues L) (pairValues L)
      (λ transverse →
        sumRational (axisValues L) (λ coordinate →
          siteField (insertAxis (sucᵢ zeroᵢ) coordinate transverse))))
    (trans
      (sumRationalCong
        (axisValues L)
        (λ x0 →
          sumRational (pairValues L) (λ pair23 →
            sumRational (axisValues L) (λ x1 →
              siteField (pair (pair x0 x1) pair23))))
        (λ x0 →
          sumRational (axisValues L) (λ x2 →
            sumRational (axisValues L) (λ x3 →
              sumRational (axisValues L) (λ x1 →
                siteField (pair (pair x0 x1) (pair x2 x3))))))
        (λ x0 →
          sumCartesian
            (axisValues L) (axisValues L)
            (λ pair23 →
              sumRational (axisValues L) (λ x1 →
                siteField (pair (pair x0 x1) pair23)))))
      (rotateAxis1ToCanonical
        (axisValues L) (axisValues L) (axisValues L) (axisValues L)
        (λ x0 x1 x2 x3 → siteField (pair (pair x0 x1) (pair x2 x3)))))

axis2PartitionMatchesCoordinateSum4 : ∀ {L} siteField →
  axisPartitionSum (sucᵢ (sucᵢ zeroᵢ)) siteField ≡ coordinateSum4 siteField
axis2PartitionMatchesCoordinateSum4 {L} siteField =
  trans
    (sumCartesian
      (axisValues L) (pairValues L)
      (λ transverse →
        sumRational (axisValues L) (λ coordinate →
          siteField (insertAxis (sucᵢ (sucᵢ zeroᵢ)) coordinate transverse))))
    (trans
      (sumRationalCong
        (axisValues L)
        (λ x0 →
          sumRational (pairValues L) (λ pair13 →
            sumRational (axisValues L) (λ x2 →
              siteField (pair (pair x0 (first pair13))
                (pair x2 (second pair13))))))
        (λ x0 →
          sumRational (axisValues L) (λ x1 →
            sumRational (axisValues L) (λ x3 →
              sumRational (axisValues L) (λ x2 →
                siteField (pair (pair x0 x1) (pair x2 x3))))))
        (λ x0 →
          sumCartesian
            (axisValues L) (axisValues L)
            (λ pair13 →
              sumRational (axisValues L) (λ x2 →
                siteField (pair (pair x0 (first pair13))
                  (pair x2 (second pair13)))))))
      (rotateAxis2ToCanonical
        (axisValues L) (axisValues L) (axisValues L) (axisValues L)
        (λ x0 x1 x2 x3 → siteField (pair (pair x0 x1) (pair x2 x3)))))
  where
  first : ∀ {A B} → Product A B → A
  first (pair left right) = left

  second : ∀ {A B} → Product A B → B
  second (pair left right) = right

axis3PartitionMatchesCoordinateSum4 : ∀ {L} siteField →
  axisPartitionSum (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField
  ≡ coordinateSum4 siteField
axis3PartitionMatchesCoordinateSum4 {L} siteField =
  trans
    (sumCartesian
      (axisValues L) (pairValues L)
      (λ transverse →
        sumRational (axisValues L) (λ coordinate →
          siteField (insertAxis (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
            coordinate transverse))))
    (sumRationalCong
      (axisValues L)
      (λ x0 →
        sumRational (pairValues L) (λ pair12 →
          sumRational (axisValues L) (λ x3 →
            siteField (pair (pair x0 (first pair12))
              (pair (second pair12) x3)))))
      (λ x0 →
        sumRational (axisValues L) (λ x1 →
          sumRational (axisValues L) (λ x2 →
            sumRational (axisValues L) (λ x3 →
              siteField (pair (pair x0 x1) (pair x2 x3))))))
      (λ x0 →
        sumCartesian
          (axisValues L) (axisValues L)
          (λ pair12 →
            sumRational (axisValues L) (λ x3 →
              siteField (pair (pair x0 (first pair12))
                (pair (second pair12) x3))))))
  where
  first : ∀ {A B} → Product A B → A
  first (pair left right) = left

  second : ∀ {A B} → Product A B → B
  second (pair left right) = right

axisPartitionMatchesCoordinateSum4 : ∀ {L} axis siteField →
  axisPartitionSum axis siteField ≡ coordinateSum4 siteField
axisPartitionMatchesCoordinateSum4 zeroᵢ siteField =
  axis0PartitionMatchesCoordinateSum4 siteField
axisPartitionMatchesCoordinateSum4 (sucᵢ zeroᵢ) siteField =
  axis1PartitionMatchesCoordinateSum4 siteField
axisPartitionMatchesCoordinateSum4 (sucᵢ (sucᵢ zeroᵢ)) siteField =
  axis2PartitionMatchesCoordinateSum4 siteField
axisPartitionMatchesCoordinateSum4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) siteField =
  axis3PartitionMatchesCoordinateSum4 siteField

axisPartitionSumMatchesGlobal : ∀ {L} axis siteField →
  axisPartitionSum axis siteField ≡ globalSiteSum siteField
axisPartitionSumMatchesGlobal axis siteField =
  trans
    (axisPartitionMatchesCoordinateSum4 axis siteField)
    (sym (globalSiteSumMatchesCoordinateSum4 siteField))

------------------------------------------------------------------------
-- Inner products and side-four average self-adjointness.
------------------------------------------------------------------------

globalBlockInner : ∀ {L} → SiteField L → SiteField L → ℚ
globalBlockInner left right =
  globalSiteSum (λ site → left site * right site)

axisPartitionInner : ∀ {L} → Axis4 → SiteField L → SiteField L → ℚ
axisPartitionInner axis left right =
  axisPartitionSum axis (λ site → left site * right site)

axisPartitionInnerMatchesGlobal : ∀ {L} axis left right →
  axisPartitionInner axis left right ≡ globalBlockInner left right
axisPartitionInnerMatchesGlobal axis left right =
  axisPartitionSumMatchesGlobal axis
    (λ site → left site * right site)

toAxisFibreField4 : Axis4 → SiteField side4 →
  FibreField (Triple (CyclicIndex side4)) (CyclicIndex side4)
toAxisFibreField4 axis siteField transverse coordinate =
  siteField (insertAxis axis coordinate transverse)

axisAverageProjectionMatchesPhysical :
  ∀ axis siteField transverse coordinate →
  fibreAverageProjection quarter (axisValues side4)
    (toAxisFibreField4 axis siteField) transverse coordinate
  ≡ axisAverage4 siteField axis (insertAxis axis coordinate transverse)
axisAverageProjectionMatchesPhysical axis siteField transverse coordinate =
  sym (axisAverage4ConstantOnFibre siteField axis transverse coordinate)

axisPartitionAverageLeftMatchesProductInner :
  ∀ axis left right →
  axisPartitionInner axis (axisAverage4 left axis) right
  ≡ productInner
      (physicalTransverseCoordinates side4)
      (axisValues side4)
      (fibreAverageProjection quarter (axisValues side4)
        (toAxisFibreField4 axis left))
      (toAxisFibreField4 axis right)
axisPartitionAverageLeftMatchesProductInner axis left right =
  sumRationalCong
    (physicalTransverseCoordinates side4)
    (λ transverse →
      sumRational (axisValues side4) (λ coordinate →
        axisAverage4 left axis (insertAxis axis coordinate transverse)
        * right (insertAxis axis coordinate transverse)))
    (λ transverse →
      sumRational (axisValues side4) (λ coordinate →
        fibreAverageProjection quarter (axisValues side4)
          (toAxisFibreField4 axis left) transverse coordinate
        * toAxisFibreField4 axis right transverse coordinate))
    (λ transverse →
      sumRationalCong
        (axisValues side4)
        (λ coordinate →
          axisAverage4 left axis (insertAxis axis coordinate transverse)
          * right (insertAxis axis coordinate transverse))
        (λ coordinate →
          fibreAverageProjection quarter (axisValues side4)
            (toAxisFibreField4 axis left) transverse coordinate
          * toAxisFibreField4 axis right transverse coordinate)
        (λ coordinate →
          congMultiplyLeft
            (sym (axisAverageProjectionMatchesPhysical
              axis left transverse coordinate))))
  where
  congMultiplyLeft : ∀ {leftValue rightValue multiplier : ℚ} →
    leftValue ≡ rightValue →
    leftValue * multiplier ≡ rightValue * multiplier
  congMultiplyLeft refl = refl

axisPartitionAverageRightMatchesProductInner :
  ∀ axis left right →
  axisPartitionInner axis left (axisAverage4 right axis)
  ≡ productInner
      (physicalTransverseCoordinates side4)
      (axisValues side4)
      (toAxisFibreField4 axis left)
      (fibreAverageProjection quarter (axisValues side4)
        (toAxisFibreField4 axis right))
axisPartitionAverageRightMatchesProductInner axis left right =
  sumRationalCong
    (physicalTransverseCoordinates side4)
    (λ transverse →
      sumRational (axisValues side4) (λ coordinate →
        left (insertAxis axis coordinate transverse)
        * axisAverage4 right axis (insertAxis axis coordinate transverse)))
    (λ transverse →
      sumRational (axisValues side4) (λ coordinate →
        toAxisFibreField4 axis left transverse coordinate
        * fibreAverageProjection quarter (axisValues side4)
            (toAxisFibreField4 axis right) transverse coordinate))
    (λ transverse →
      sumRationalCong
        (axisValues side4)
        (λ coordinate →
          left (insertAxis axis coordinate transverse)
          * axisAverage4 right axis (insertAxis axis coordinate transverse))
        (λ coordinate →
          toAxisFibreField4 axis left transverse coordinate
          * fibreAverageProjection quarter (axisValues side4)
              (toAxisFibreField4 axis right) transverse coordinate)
        (λ coordinate →
          congMultiplyRight
            (sym (axisAverageProjectionMatchesPhysical
              axis right transverse coordinate))))
  where
  congMultiplyRight : ∀ {leftValue rightValue multiplier : ℚ} →
    leftValue ≡ rightValue →
    multiplier * leftValue ≡ multiplier * rightValue
  congMultiplyRight refl = refl

physicalAxisAverage4SelfAdjoint : ∀ axis left right →
  globalBlockInner (axisAverage4 left axis) right
  ≡ globalBlockInner left (axisAverage4 right axis)
physicalAxisAverage4SelfAdjoint axis left right =
  trans
    (sym (axisPartitionInnerMatchesGlobal axis
      (axisAverage4 left axis) right))
    (trans
      (axisPartitionAverageLeftMatchesProductInner axis left right)
      (trans
        (finiteFibreAverageSelfAdjoint
          quarter
          (physicalTransverseCoordinates side4)
          (axisValues side4)
          (toAxisFibreField4 axis left)
          (toAxisFibreField4 axis right))
        (trans
          (sym (axisPartitionAverageRightMatchesProductInner
            axis left right))
          (axisPartitionInnerMatchesGlobal axis
            left (axisAverage4 right axis)))))

physicalAxisPartitionInnerProductMatchLevel : ProofLevel
physicalAxisPartitionInnerProductMatchLevel = machineChecked

path4PhysicalAxisAverageSelfAdjointnessLevel : ProofLevel
path4PhysicalAxisAverageSelfAdjointnessLevel = machineChecked

physicalArbitrarySideAverageNormalizationLevel : ProofLevel
physicalArbitrarySideAverageNormalizationLevel = conditional
