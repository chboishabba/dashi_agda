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
--
-- This is stronger than both the old side-four 29/1024 floor and the earlier
-- conservative L=13 candidate 101/3072, while remaining on the same
-- 342732-coordinate state carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
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
  let
    witness = flat - (+ 4 / 1) * defect
    nonnegative = FiniteL2.squareNonnegative witness
  in
  subst
    (λ candidate → candidate ≤ sq (flat + defect))
    (ℚRing.solve-∀ flat defect)
    (ℚP.≤-trans
      (subst
        (λ candidate → 0ℚ ≤ candidate)
        (ℚRing.solve-∀ flat defect)
        nonnegative)
      (ℚP.≤-refl))

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
        - (+ 3 / 1) * sq (Background.gaugeAdjointDefect13 background multiplier state))
      (λ state →
        sq (selectedBackgroundGaugeAdjoint13 background multiplier state))
      (λ state →
        scalarYoungLowerQuarter
          (Flat.flatGaugeAdjoint13 multiplier state)
          (Background.gaugeAdjointDefect13 background multiplier state))

    leftExact :
      sumRational (Physical.physicalSU2Coordinates Side13.side13)
        (λ state →
          threeQuarter * sq (Flat.flatGaugeAdjoint13 multiplier state)
          - (+ 3 / 1) * sq (Background.gaugeAdjointDefect13 background multiplier state))
      ≡ threeQuarter * Flat.flatGaugeAdjointNormSq13 multiplier
        - (+ 3 / 1) * Background.gaugeAdjointDefectNormSq13 background multiplier
    leftExact = finiteScaledDifference
      (Physical.physicalSU2Coordinates Side13.side13)
      (λ state → sq (Flat.flatGaugeAdjoint13 multiplier state))
      (λ state → sq (Background.gaugeAdjointDefect13 background multiplier state))
  in
  subst
    (λ lower → lower ≤ selectedBackgroundGaugeAdjointNormSq13 background multiplier)
    leftExact pointwise
  where
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

selectedBackgroundGaugeAdjointFloor13 :
  ∀ background → Background.SelectedInverseLinkRadius13 background →
  ∀ multiplier → FlatFloor.FlatGaugeReducedMultiplier13 multiplier →
  selectedGaugeFloor13 * FlatFloor.gaugeMultiplierNormSq13 multiplier
  ≤ selectedBackgroundGaugeAdjointNormSq13 background multiplier
selectedBackgroundGaugeAdjointFloor13 background radius multiplier reduced =
  let
    flatFloor = FlatFloor.flatGaugeAdjointPoincareFloor13 multiplier reduced
    defectUpper = Background.selectedGaugeAdjointDefectBound13
      background radius multiplier

    scaledFlat =
      Background.Norm.scaleNonnegative threeQuarter
        (ℚP.nonNegative⁻¹ threeQuarter) flatFloor

    negativeDefect :
      - ((+ 3 / 1) * Background.gaugeAdjointDefectNormSq13 background multiplier)
      ≤ - ((+ 3 / 1) *
        (Background.selectedAdjointDefectCoefficient13
          * FlatFloor.gaugeMultiplierNormSq13 multiplier))
    negativeDefect =
      let
        scaled = Background.Norm.scaleNonnegative (+ 3 / 1)
          (ℚP.nonNegative⁻¹ (+ 3 / 1)) defectUpper
      in
      ℚP.neg-mono-≤ scaled

    combined = ℚP.+-mono-≤ scaledFlat negativeDefect

    lowerExact :
      selectedGaugeFloor13 * FlatFloor.gaugeMultiplierNormSq13 multiplier
      ≡ threeQuarter * (LDL.oneEighteenth
          * FlatFloor.gaugeMultiplierNormSq13 multiplier)
        + (- ((+ 3 / 1) * Background.gaugeAdjointDefectNormSq13 background multiplier))
        + remainder
    lowerExact = ℚRing.solve-∀
      (FlatFloor.gaugeMultiplierNormSq13 multiplier)
      (Background.gaugeAdjointDefectNormSq13 background multiplier)
    where
    remainder : ℚ
    remainder =
      (+ 3 / 1) * Background.gaugeAdjointDefectNormSq13 background multiplier
      - (+ 3 / 1) * Background.selectedAdjointDefectCoefficient13
          * FlatFloor.gaugeMultiplierNormSq13 multiplier
  in
  subst
    (λ lower → lower ≤ selectedBackgroundGaugeAdjointNormSq13 background multiplier)
    (selectedLowerExact
      (FlatFloor.gaugeMultiplierNormSq13 multiplier)
      (Background.gaugeAdjointDefectNormSq13 background multiplier))
    (ℚP.≤-trans
      (ℚP.+-mono-≤ scaledFlat negativeDefect)
      (summedYoungLower background multiplier))
  where
  selectedLowerExact : ∀ norm defectNorm →
    selectedGaugeFloor13 * norm
    ≡ threeQuarter * (LDL.oneEighteenth * norm)
      - (+ 3 / 1) *
          (Background.selectedAdjointDefectCoefficient13 * norm)
  selectedLowerExact norm defectNorm
    rewrite sym selectedGaugeFloorArithmetic =
    ℚRing.solve-∀ norm

path13SelectedBackgroundGaugeAdjointFloorLevel : ProofLevel
path13SelectedBackgroundGaugeAdjointFloorLevel = machineChecked
