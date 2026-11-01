module DASHI.Physics.YangMills.BalabanPath13PreconditionedSelectedCombinedFloorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Perturb the exact preconditioned flat combined normal by the literal L=13
-- background gauge adjoint defect.  The flat average+gauge pair has floor
-- 1/18 on the reduced multiplier carrier.  The selected background defect
-- acts only on the gauge multiplier and has squared norm coefficient
-- 9/1048576.  Since ||gamma||^2 <= ||(alpha,gamma)||^2, pointwise Young gives
--
--   (130991/3145728) ||(alpha,gamma)||^2
--      <= ||(169 Q)^* alpha + L_g,A^* gamma||^2.
--
-- Thus the source-scale reduced normal is quantitatively coercive without a
-- 342732-dimensional Gram computation.  This theorem concerns the literal
-- normalized block-average plus gauge constraint.  Identifying the full
-- nonlinear CMP109 equation-(0.12) derivative with its local four-stage
-- kernel remains a separate same-object theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanPhysicalBlockAverageConstraintMatrixExact as BlockAverage
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanCMP109L13BlockAverageAdjointFloorExact as Average
import DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointMatrixExact as Flat
import DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointPoincareFloorExact as GaugeFloor
import DASHI.Physics.YangMills.BalabanPath13PreconditionedFlatCombinedFloorExact as FlatCombined
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundGaugeAdjointFloorExact as GaugeSelected

selectedCombinedAdjoint13 :
  Background.RationalSU2Background13 →
  FlatCombined.CombinedMultiplier13 → Average.StateVector
selectedCombinedAdjoint13 background multiplier state =
  FlatCombined.combinedAdjoint13 multiplier state
  + Background.gaugeAdjointDefect13
      background (FlatCombined.gaugeMultiplier multiplier) state

selectedCombinedAdjointNormSq13 :
  Background.RationalSU2Background13 →
  FlatCombined.CombinedMultiplier13 → ℚ
selectedCombinedAdjointNormSq13 background multiplier =
  Average.stateNormSq (selectedCombinedAdjoint13 background multiplier)

averageRowNormNonnegative : ∀ multiplier →
  0ℚ ≤ Average.rowNormSq multiplier
averageRowNormNonnegative multiplier =
  Schur.sumNonnegative BlockAverage.selectedBlockAverageRows
    (λ row → sq (multiplier row))
    (λ row → FiniteL2.squareNonnegative (multiplier row))

gaugeNormBelowCombined : ∀ multiplier →
  GaugeFloor.gaugeMultiplierNormSq13 (FlatCombined.gaugeMultiplier multiplier)
  ≤ FlatCombined.combinedRowNormSq13 multiplier
gaugeNormBelowCombined multiplier =
  let
    averageNorm = Average.rowNormSq (FlatCombined.averageMultiplier multiplier)
    gaugeNorm = GaugeFloor.gaugeMultiplierNormSq13
      (FlatCombined.gaugeMultiplier multiplier)
  in
  subst
    (λ upper → gaugeNorm ≤ upper)
    (ℚRing.solve-∀ averageNorm gaugeNorm)
    (ℚP.+-monoˡ-≤ gaugeNorm
      (averageRowNormNonnegative (FlatCombined.averageMultiplier multiplier)))

selectedCombinedDefectBound13 :
  ∀ background → Background.SelectedInverseLinkRadius13 background →
  ∀ multiplier →
  Background.gaugeAdjointDefectNormSq13
      background (FlatCombined.gaugeMultiplier multiplier)
  ≤ Background.selectedAdjointDefectCoefficient13
      * FlatCombined.combinedRowNormSq13 multiplier
selectedCombinedDefectBound13 background radius multiplier =
  let
    gaugeBound = Background.selectedGaugeAdjointDefectBound13
      background radius (FlatCombined.gaugeMultiplier multiplier)
    coefficient = Background.selectedAdjointDefectCoefficient13
    coefficientNonnegative = ℚP.nonNegative⁻¹ coefficient
    enlarged = Norm.scaleNonnegative coefficient coefficientNonnegative
      (gaugeNormBelowCombined multiplier)
  in
  ℚP.≤-trans gaugeBound enlarged

scalarYoungLowerQuarter : ∀ flat defect →
  (+ 3 / 4) * sq flat - (+ 3 / 1) * sq defect
  ≤ sq (flat + defect)
scalarYoungLowerQuarter = GaugeSelected.scalarYoungLowerQuarter

finiteScaledDifference :
  ∀ {A : Set} (values : Agda.Builtin.List.List A)
    (left right : A → ℚ) →
  sumRational values
    (λ value → (+ 3 / 4) * left value - (+ 3 / 1) * right value)
  ≡ (+ 3 / 4) * sumRational values left
    - (+ 3 / 1) * sumRational values right
finiteScaledDifference Agda.Builtin.List.[] left right = ℚRing.solve []
finiteScaledDifference (Agda.Builtin.List._∷_ value values) left right
  rewrite finiteScaledDifference values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (sumRational values left) (sumRational values right)

summedCombinedYoungLower : ∀ background multiplier →
  (+ 3 / 4) * FlatCombined.combinedAdjointNormSq13 multiplier
    - (+ 3 / 1) * Background.gaugeAdjointDefectNormSq13
        background (FlatCombined.gaugeMultiplier multiplier)
  ≤ selectedCombinedAdjointNormSq13 background multiplier
summedCombinedYoungLower background multiplier =
  let
    defect = Background.gaugeAdjointDefect13
      background (FlatCombined.gaugeMultiplier multiplier)
    flat = FlatCombined.combinedAdjoint13 multiplier
    pointwise = Schur.sumPointwiseBelow
      (Physical.physicalSU2Coordinates Side13.side13)
      (λ state → (+ 3 / 4) * sq (flat state) - (+ 3 / 1) * sq (defect state))
      (λ state → sq (flat state + defect state))
      (λ state → scalarYoungLowerQuarter (flat state) (defect state))
  in
  subst
    (λ lower → lower ≤ selectedCombinedAdjointNormSq13 background multiplier)
    (finiteScaledDifference
      (Physical.physicalSU2Coordinates Side13.side13)
      (λ state → sq (flat state))
      (λ state → sq (defect state)))
    pointwise

selectedCombinedFloor13 : ℚ
selectedCombinedFloor13 = GaugeSelected.selectedGaugeFloor13

preconditionedSelectedCombinedFloor13 :
  ∀ background → Background.SelectedInverseLinkRadius13 background →
  ∀ multiplier → FlatCombined.ReducedCombinedMultiplier13 multiplier →
  selectedCombinedFloor13 * FlatCombined.combinedRowNormSq13 multiplier
  ≤ selectedCombinedAdjointNormSq13 background multiplier
preconditionedSelectedCombinedFloor13 background radius multiplier reduced =
  let
    norm = FlatCombined.combinedRowNormSq13 multiplier
    flatNorm = FlatCombined.combinedAdjointNormSq13 multiplier
    defectNorm = Background.gaugeAdjointDefectNormSq13
      background (FlatCombined.gaugeMultiplier multiplier)
    flatFloor = FlatCombined.preconditionedFlatCombinedFloor13 multiplier reduced
    defectUpper = selectedCombinedDefectBound13 background radius multiplier

    scaledFlat = Norm.scaleNonnegative (+ 3 / 4)
      (ℚP.nonNegative⁻¹ (+ 3 / 4)) flatFloor
    scaledDefect = Norm.scaleNonnegative (+ 3 / 1)
      (ℚP.nonNegative⁻¹ (+ 3 / 1)) defectUpper
    negativeDefect = ℚP.neg-mono-≤ scaledDefect
    combined = ℚP.+-mono-≤ scaledFlat negativeDefect

    candidateExact :
      selectedCombinedFloor13 * norm
      ≡ (+ 3 / 4) * (LDL.oneEighteenth * norm)
        + (- ((+ 3 / 1) *
          (Background.selectedAdjointDefectCoefficient13 * norm)))
    candidateExact
      rewrite sym GaugeSelected.selectedGaugeFloorArithmetic =
      ℚRing.solve-∀ norm

    youngFormExact :
      (+ 3 / 4) * flatNorm + (- ((+ 3 / 1) * defectNorm))
      ≡ (+ 3 / 4) * flatNorm - (+ 3 / 1) * defectNorm
    youngFormExact = ℚRing.solve-∀ flatNorm defectNorm
  in
  subst
    (λ lower → lower ≤ selectedCombinedAdjointNormSq13 background multiplier)
    candidateExact
    (ℚP.≤-trans combined
      (subst
        (λ lower → lower ≤ selectedCombinedAdjointNormSq13 background multiplier)
        youngFormExact
        (summedCombinedYoungLower background multiplier)))

path13PreconditionedSelectedCombinedFloorLevel : ProofLevel
path13PreconditionedSelectedCombinedFloorLevel = machineChecked
