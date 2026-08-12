module DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundGaugeAdjointFloorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Combine the literal source-scale flat gauge floor with the selected-radius
-- L=13 background adjoint defect.  Pointwise Young with eta=1/4 gives
--
--   |r+d|^2 >= (3/4)|r|^2 - 3|d|^2.
--
-- Using
--
--   |r|^2 >= (1/18)|gamma|^2,
--   |d|^2 <= (9/1048576)|gamma|^2,
--
-- yields the exact selected-background floor
--
--   (130991/3145728)|gamma|^2
--      <= |L_g,A^* gamma|^2.
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
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointMatrixExact as Flat
import DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointPoincareFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background

selectedBackgroundGaugeAdjoint13 :
  Background.RationalSU2Background13 → Flat.GaugeMultiplier13 →
  Background.StateVector13
selectedBackgroundGaugeAdjoint13 background multiplier state =
  Flat.flatGaugeAdjoint13 multiplier state
  + Background.gaugeAdjointDefect13 background multiplier state

selectedBackgroundGaugeAdjointNormSq13 :
  Background.RationalSU2Background13 → Flat.GaugeMultiplier13 → ℚ
selectedBackgroundGaugeAdjointNormSq13 background multiplier =
  Physical.physicalSU2CoordinateNormSq
    (selectedBackgroundGaugeAdjoint13 background multiplier)

threeQuarter : ℚ
threeQuarter = + 3 / 4

selectedGaugeFloor13 : ℚ
selectedGaugeFloor13 = + 130991 / 3145728

selectedGaugeFloorArithmetic :
  threeQuarter * LDL.oneEighteenth
    - (+ 3 / 1) * Background.selectedAdjointDefectCoefficient13
  ≡ selectedGaugeFloor13
selectedGaugeFloorArithmetic = ℚRing.solve []

scalarYoungLowerQuarter : ∀ flat defect →
  threeQuarter * sq flat - (+ 3 / 1) * sq defect
  ≤ sq (flat + defect)
scalarYoungLowerQuarter flat defect =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ candidate → 0ℚ ≤ candidate)
      (ℚRing.solve-∀ flat defect)
      (FiniteL2.squareNonnegative
        ((+ 1 / 2) * flat + (+ 2 / 1) * defect)))

finiteScaledDifference :
  ∀ {A : Set} (values : Agda.Builtin.List.List A)
    (left right : A → ℚ) →
  sumRational values
    (λ value → threeQuarter * left value - (+ 3 / 1) * right value)
  ≡ threeQuarter * sumRational values left
    - (+ 3 / 1) * sumRational values right
finiteScaledDifference Agda.Builtin.List.[] left right = ℚRing.solve []
finiteScaledDifference (Agda.Builtin.List._∷_ value values) left right
  rewrite finiteScaledDifference values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (sumRational values left) (sumRational values right)

summedYoungLower : ∀ background multiplier →
  threeQuarter * Flat.flatGaugeAdjointNormSq13 multiplier
    - (+ 3 / 1) * Background.gaugeAdjointDefectNormSq13 background multiplier
  ≤ selectedBackgroundGaugeAdjointNormSq13 background multiplier
summedYoungLower background multiplier =
  let
    pointwise = Schur.sumPointwiseBelow
      (Physical.physicalSU2Coordinates Side13.side13)
      (λ state →
        threeQuarter * sq (Flat.flatGaugeAdjoint13 multiplier state)
        - (+ 3 / 1) * sq
            (Background.gaugeAdjointDefect13 background multiplier state))
      (λ state →
        sq (selectedBackgroundGaugeAdjoint13 background multiplier state))
      (λ state →
        scalarYoungLowerQuarter
          (Flat.flatGaugeAdjoint13 multiplier state)
          (Background.gaugeAdjointDefect13 background multiplier state))

    leftExact = finiteScaledDifference
      (Physical.physicalSU2Coordinates Side13.side13)
      (λ state → sq (Flat.flatGaugeAdjoint13 multiplier state))
      (λ state → sq (Background.gaugeAdjointDefect13 background multiplier state))
  in
  subst
    (λ lower → lower ≤ selectedBackgroundGaugeAdjointNormSq13 background multiplier)
    leftExact pointwise

selectedBackgroundGaugeAdjointFloor13 :
  ∀ background → Background.SelectedInverseLinkRadius13 background →
  ∀ multiplier → FlatFloor.FlatGaugeReducedMultiplier13 multiplier →
  selectedGaugeFloor13 * FlatFloor.gaugeMultiplierNormSq13 multiplier
  ≤ selectedBackgroundGaugeAdjointNormSq13 background multiplier
selectedBackgroundGaugeAdjointFloor13 background radius multiplier reduced =
  let
    norm = FlatFloor.gaugeMultiplierNormSq13 multiplier
    flatNorm = Flat.flatGaugeAdjointNormSq13 multiplier
    defectNorm = Background.gaugeAdjointDefectNormSq13 background multiplier

    flatFloor = FlatFloor.flatGaugeAdjointPoincareFloor13 multiplier reduced
    defectUpper = Background.selectedGaugeAdjointDefectBound13
      background radius multiplier

    scaledFlat :
      threeQuarter * (LDL.oneEighteenth * norm)
      ≤ threeQuarter * flatNorm
    scaledFlat = Norm.scaleNonnegative threeQuarter
      (ℚP.nonNegative⁻¹ threeQuarter) flatFloor

    scaledDefect :
      (+ 3 / 1) * defectNorm
      ≤ (+ 3 / 1) *
          (Background.selectedAdjointDefectCoefficient13 * norm)
    scaledDefect = Norm.scaleNonnegative (+ 3 / 1)
      (ℚP.nonNegative⁻¹ (+ 3 / 1)) defectUpper

    negativeDefect :
      - ((+ 3 / 1) *
          (Background.selectedAdjointDefectCoefficient13 * norm))
      ≤ - ((+ 3 / 1) * defectNorm)
    negativeDefect = ℚP.neg-mono-≤ scaledDefect

    combined :
      threeQuarter * (LDL.oneEighteenth * norm)
        + (- ((+ 3 / 1) *
          (Background.selectedAdjointDefectCoefficient13 * norm)))
      ≤ threeQuarter * flatNorm + (- ((+ 3 / 1) * defectNorm))
    combined = ℚP.+-mono-≤ scaledFlat negativeDefect

    candidateExact :
      selectedGaugeFloor13 * norm
      ≡ threeQuarter * (LDL.oneEighteenth * norm)
        + (- ((+ 3 / 1) *
          (Background.selectedAdjointDefectCoefficient13 * norm)))
    candidateExact
      rewrite sym selectedGaugeFloorArithmetic = ℚRing.solve-∀ norm

    youngFormExact :
      threeQuarter * flatNorm + (- ((+ 3 / 1) * defectNorm))
      ≡ threeQuarter * flatNorm - (+ 3 / 1) * defectNorm
    youngFormExact = ℚRing.solve-∀ flatNorm defectNorm
  in
  subst
    (λ lower → lower ≤ selectedBackgroundGaugeAdjointNormSq13 background multiplier)
    candidateExact
    (ℚP.≤-trans combined
      (subst
        (λ lower → lower ≤ selectedBackgroundGaugeAdjointNormSq13 background multiplier)
        youngFormExact
        (summedYoungLower background multiplier)))

path13SelectedBackgroundGaugeAdjointFloorLevel : ProofLevel
path13SelectedBackgroundGaugeAdjointFloorLevel = machineChecked
