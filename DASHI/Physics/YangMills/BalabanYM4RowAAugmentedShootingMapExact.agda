{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingMapExact where

------------------------------------------------------------------------
-- ROW A: q_direct + q_history < 1 -> ACTUAL SHOOTING-MAP CONTRACTION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 1ℚ; ∣_∣; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingGateExact as Aug

record AugmentedShootingMapData (cutoff : Nat) : Set₁ where
  field
    sensitivityData : Aug.AugmentedShootingSensitivityData cutoff
    cutoffIndex : Nat
    cutoffIndexBelow : cutoffIndex ℕ.≤ cutoff

    directCorrection irrelevantHistoryCorrection : ℚ → ℚ

    directCorrectionLipschitz : ∀ u v →
      ∣ directCorrection u - directCorrection v ∣
      ≤ Aug.Augmented.qDirect sensitivityData cutoffIndex * ∣ u - v ∣

    irrelevantHistoryLipschitz : ∀ u v →
      ∣ irrelevantHistoryCorrection u - irrelevantHistoryCorrection v ∣
      ≤ Aug.Augmented.qHistory sensitivityData * ∣ u - v ∣

open AugmentedShootingMapData public

totalCorrection : ∀ {cutoff} → AugmentedShootingMapData cutoff → ℚ → ℚ
totalCorrection dataSet u =
  directCorrection dataSet u + irrelevantHistoryCorrection dataSet u

totalCorrectionDifferenceSplit :
  ∀ {cutoff} (dataSet : AugmentedShootingMapData cutoff) u v →
  totalCorrection dataSet u - totalCorrection dataSet v
  ≡ (directCorrection dataSet u - directCorrection dataSet v)
    + (irrelevantHistoryCorrection dataSet u
      - irrelevantHistoryCorrection dataSet v)
totalCorrectionDifferenceSplit dataSet u v =
  ℚRing.solve-∀
    (directCorrection dataSet u)
    (irrelevantHistoryCorrection dataSet u)
    (directCorrection dataSet v)
    (irrelevantHistoryCorrection dataSet v)

totalCorrectionLipschitz :
  ∀ {cutoff} (dataSet : AugmentedShootingMapData cutoff) u v →
  ∣ totalCorrection dataSet u - totalCorrection dataSet v ∣
  ≤ Aug.Augmented.qTotal (sensitivityData dataSet) (cutoffIndex dataSet)
      * ∣ u - v ∣
totalCorrectionLipschitz dataSet u v =
  let
    directDifference = directCorrection dataSet u - directCorrection dataSet v
    historyDifference =
      irrelevantHistoryCorrection dataSet u - irrelevantHistoryCorrection dataSet v

    splitAbs :
      ∣ totalCorrection dataSet u - totalCorrection dataSet v ∣
      ≡ ∣ directDifference + historyDifference ∣
    splitAbs = cong ∣_∣ (totalCorrectionDifferenceSplit dataSet u v)

    triangle :
      ∣ directDifference + historyDifference ∣
      ≤ ∣ directDifference ∣ + ∣ historyDifference ∣
    triangle = ℚP.∣p+q∣≤∣p∣+∣q∣ directDifference historyDifference

    componentBounds = ℚP.+-mono-≤
      (directCorrectionLipschitz dataSet u v)
      (irrelevantHistoryLipschitz dataSet u v)

    targetShape :
      Aug.Augmented.qDirect (sensitivityData dataSet) (cutoffIndex dataSet)
          * ∣ u - v ∣
        + Aug.Augmented.qHistory (sensitivityData dataSet) * ∣ u - v ∣
      ≡ Aug.Augmented.qTotal
          (sensitivityData dataSet) (cutoffIndex dataSet)
          * ∣ u - v ∣
    targetShape = ℚRing.solve-∀
      (Aug.Augmented.qDirect (sensitivityData dataSet) (cutoffIndex dataSet))
      (Aug.Augmented.qHistory (sensitivityData dataSet))
      ∣ u - v ∣
  in
  subst
    (λ left → left ≤
      Aug.Augmented.qTotal (sensitivityData dataSet) (cutoffIndex dataSet)
        * ∣ u - v ∣)
    (sym splitAbs)
    (ℚP.≤-trans triangle
      (subst
        (λ right →
          ∣ directDifference ∣ + ∣ historyDifference ∣ ≤ right)
        targetShape
        componentBounds))

strictTotalSensitivity :
  ∀ {cutoff} (dataSet : AugmentedShootingMapData cutoff) →
  Aug.Augmented.qTotal (sensitivityData dataSet) (cutoffIndex dataSet) < 1ℚ
strictTotalSensitivity dataSet =
  Aug.Augmented.qTotalBelowOne
    (sensitivityData dataSet)
    (cutoffIndex dataSet)
    (cutoffIndexBelow dataSet)

shootingMapContraction :
  ∀ {cutoff} (dataSet : AugmentedShootingMapData cutoff)
    (target u v : ℚ) →
  ∣ (target + totalCorrection dataSet u)
      - (target + totalCorrection dataSet v) ∣
  ≤ Aug.Augmented.qTotal (sensitivityData dataSet) (cutoffIndex dataSet)
      * ∣ u - v ∣
shootingMapContraction dataSet target =
  Direct.shootingContraction
    target
    (totalCorrection dataSet)
    (totalCorrectionLipschitz dataSet)

shootingMapStrictContractionPackage :
  ∀ {cutoff} (dataSet : AugmentedShootingMapData cutoff)
    (target u v : ℚ) →
  (∣ (target + totalCorrection dataSet u)
      - (target + totalCorrection dataSet v) ∣
    ≤ Aug.Augmented.qTotal (sensitivityData dataSet) (cutoffIndex dataSet)
      * ∣ u - v ∣)
  × (Aug.Augmented.qTotal
      (sensitivityData dataSet) (cutoffIndex dataSet) < 1ℚ)
shootingMapStrictContractionPackage dataSet target u v =
  shootingMapContraction dataSet target u v , strictTotalSensitivity dataSet

rowAAugmentedCorrectionLipschitzAssemblyLevel : ProofLevel
rowAAugmentedCorrectionLipschitzAssemblyLevel = machineChecked

rowAAugmentedShootingMapStrictContractionLevel : ProofLevel
rowAAugmentedShootingMapStrictContractionLevel = machineChecked

literalRowAAugmentedShootingMapIdentificationLevel : ProofLevel
literalRowAAugmentedShootingMapIdentificationLevel = conditional
