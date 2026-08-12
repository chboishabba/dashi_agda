module DASHI.Physics.Closure.NSTriadKNHHDirectionalDefectPackingRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Zoran Grujic.
-- Title: "A Geometric Measure-Type Regularity Criterion for Solutions to the
-- 3D Navier-Stokes Equations".
-- DOI: 10.1088/0951-7715/26/1/289.
-- arXiv DOI: 10.48550/arXiv.1111.0217.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- The Round-41 full classified carrier made
--
--   D_dir = D_good + D_bad,
--   delta E_bad <= D_bad <= D_dir
--
-- exact on the same physical cells.  The attached analysis suggested testing
-- a shell-time/Carleson-style packing theorem for D_dir rather than proving
-- unrelated good and bad occupation estimates.
--
-- This file proves the exact finite reduction needed for that experiment.
-- For any finite family of boxes, one common directional-defect packing bound
--
--   sum_box D_dir(box) <= P
--
-- simultaneously implies
--
--   sum_box E_bad(box) <= delta^-1 P
--
-- and, whenever each good production square obeys
--
--   G_box^2 <= C_good delta D_good(box),
--
--   sum_box G_box^2 <= C_good delta P.
--
-- Thus one genuine physical packing theorem on the master defect measure can
-- feed both HH strata.  No Carleson estimate is asserted here: the new hard
-- physical producer is precisely the cutoff-uniform shell-time packing bound
-- for the actual Navier-Stokes defect boxes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHDirectionalDefectSharedBudgetRound41Exact as Shared

record DirectionalDefectPackingBox
    (parameter : Threshold.PositiveThreshold)
    (goodCoefficient : ℚ) : Set where
  field
    cells : List (Shared.ClassifiedDirectionalEnergyCell parameter)
    goodProductionSquare : ℚ
    goodProductionSquareNonnegative : 0ℚ ≤ goodProductionSquare
    goodSquareBelowLocalGoodDefect :
      goodProductionSquare
      ≤ goodCoefficient * Threshold.threshold parameter
          * Shared.goodDirectionalDefectMass cells

open DirectionalDefectPackingBox public

sumBoxDefect :
  ∀ {parameter goodCoefficient} →
  List (DirectionalDefectPackingBox parameter goodCoefficient) → ℚ
sumBoxDefect [] = 0ℚ
sumBoxDefect (box ∷ rest) =
  Shared.totalDirectionalDefectMass (cells box) + sumBoxDefect rest

sumBoxGoodDefect :
  ∀ {parameter goodCoefficient} →
  List (DirectionalDefectPackingBox parameter goodCoefficient) → ℚ
sumBoxGoodDefect [] = 0ℚ
sumBoxGoodDefect (box ∷ rest) =
  Shared.goodDirectionalDefectMass (cells box) + sumBoxGoodDefect rest

sumBoxBadEnergy :
  ∀ {parameter goodCoefficient} →
  List (DirectionalDefectPackingBox parameter goodCoefficient) → ℚ
sumBoxBadEnergy [] = 0ℚ
sumBoxBadEnergy (box ∷ rest) =
  Shared.badEnergyMass (cells box) + sumBoxBadEnergy rest

sumGoodProductionSquare :
  ∀ {parameter goodCoefficient} →
  List (DirectionalDefectPackingBox parameter goodCoefficient) → ℚ
sumGoodProductionSquare [] = 0ℚ
sumGoodProductionSquare (box ∷ rest) =
  goodProductionSquare box + sumGoodProductionSquare rest

sumGoodDefectBelowTotalDefect :
  ∀ {parameter goodCoefficient}
    (boxes : List (DirectionalDefectPackingBox parameter goodCoefficient)) →
  sumBoxGoodDefect boxes ≤ sumBoxDefect boxes
sumGoodDefectBelowTotalDefect [] = ℚP.≤-refl
sumGoodDefectBelowTotalDefect (box ∷ rest) =
  ℚP.+-mono-≤
    (Shared.goodDefectMassBelowTotalDefect (cells box))
    (sumGoodDefectBelowTotalDefect rest)

thresholdTimesPackedBadEnergyBelowPackedDefect :
  ∀ {parameter goodCoefficient}
    (boxes : List (DirectionalDefectPackingBox parameter goodCoefficient)) →
  Threshold.threshold parameter * sumBoxBadEnergy boxes
  ≤ sumBoxDefect boxes
thresholdTimesPackedBadEnergyBelowPackedDefect {parameter} [] =
  subst
    (λ lower → lower ≤ 0ℚ)
    (solve (Threshold.threshold parameter ∷ []))
    ℚP.≤-refl
thresholdTimesPackedBadEnergyBelowPackedDefect
    {parameter} (box ∷ rest) =
  let
    local = Shared.thresholdTimesBadEnergyBelowTotalDefect (cells box)
    tail = thresholdTimesPackedBadEnergyBelowPackedDefect rest
    added = ℚP.+-mono-≤ local tail

    leftMeaning :
      Threshold.threshold parameter
        * (Shared.badEnergyMass (cells box) + sumBoxBadEnergy rest)
      ≡ Threshold.threshold parameter * Shared.badEnergyMass (cells box)
        + Threshold.threshold parameter * sumBoxBadEnergy rest
    leftMeaning = solve
      ( Threshold.threshold parameter
      ∷ Shared.badEnergyMass (cells box)
      ∷ sumBoxBadEnergy rest
      ∷ [])
  in
  subst
    (λ lower → lower ≤ sumBoxDefect (box ∷ rest))
    (sym leftMeaning)
    added

sumGoodSquaresBelowGoodDefect :
  ∀ {parameter goodCoefficient}
    (coefficientNonnegative : 0ℚ ≤ goodCoefficient)
    (boxes : List (DirectionalDefectPackingBox parameter goodCoefficient)) →
  sumGoodProductionSquare boxes
  ≤ goodCoefficient * Threshold.threshold parameter
      * sumBoxGoodDefect boxes
sumGoodSquaresBelowGoodDefect {parameter} {goodCoefficient} coefficientNN [] =
  subst
    (λ upper → 0ℚ ≤ upper)
    (solve (goodCoefficient ∷ Threshold.threshold parameter ∷ []))
    ℚP.≤-refl
sumGoodSquaresBelowGoodDefect
    {parameter} {goodCoefficient} coefficientNN (box ∷ rest) =
  let
    tail = sumGoodSquaresBelowGoodDefect coefficientNN rest
    added = ℚP.+-mono-≤ (goodSquareBelowLocalGoodDefect box) tail

    rightMeaning :
      goodCoefficient * Threshold.threshold parameter
          * Shared.goodDirectionalDefectMass (cells box)
      + goodCoefficient * Threshold.threshold parameter
          * sumBoxGoodDefect rest
      ≡ goodCoefficient * Threshold.threshold parameter
          * sumBoxGoodDefect (box ∷ rest)
    rightMeaning = solve
      ( goodCoefficient
      ∷ Threshold.threshold parameter
      ∷ Shared.goodDirectionalDefectMass (cells box)
      ∷ sumBoxGoodDefect rest
      ∷ [])
  in
  subst
    (λ upper → sumGoodProductionSquare (box ∷ rest) ≤ upper)
    rightMeaning
    added

record DirectionalDefectPackingCertificate
    (parameter : Threshold.PositiveThreshold)
    (goodCoefficient : ℚ) : Set where
  field
    boxes : List (DirectionalDefectPackingBox parameter goodCoefficient)
    packingEnvelope : ℚ
    goodCoefficientNonnegative : 0ℚ ≤ goodCoefficient
    defectPackingBound : sumBoxDefect boxes ≤ packingEnvelope

open DirectionalDefectPackingCertificate public

packedBadEnergyBelowInverseThresholdEnvelope :
  ∀ {parameter goodCoefficient} →
  (certificate : DirectionalDefectPackingCertificate
    parameter goodCoefficient) →
  sumBoxBadEnergy (boxes certificate)
  ≤ Threshold.thresholdInverse parameter * packingEnvelope certificate
packedBadEnergyBelowInverseThresholdEnvelope
    {parameter} certificate =
  let
    thresholdBound = thresholdTimesPackedBadEnergyBelowPackedDefect
      (boxes certificate)
    toEnvelope = ℚP.≤-trans thresholdBound (defectPackingBound certificate)

    scaled :
      Threshold.thresholdInverse parameter
        * (Threshold.threshold parameter * sumBoxBadEnergy (boxes certificate))
      ≤ Threshold.thresholdInverse parameter * packingEnvelope certificate
    scaled =
      let instance inverseNN = nonNegative
            (Threshold.thresholdInverseNonnegative parameter)
      in ℚP.*-monoˡ-≤-nonNeg
        (Threshold.thresholdInverse parameter) toEnvelope

    leftRegroup :
      Threshold.thresholdInverse parameter
        * (Threshold.threshold parameter * sumBoxBadEnergy (boxes certificate))
      ≡ (Threshold.thresholdInverse parameter * Threshold.threshold parameter)
          * sumBoxBadEnergy (boxes certificate)
    leftRegroup = solve
      ( Threshold.thresholdInverse parameter
      ∷ Threshold.threshold parameter
      ∷ sumBoxBadEnergy (boxes certificate)
      ∷ [])

    leftCancel :
      (Threshold.thresholdInverse parameter * Threshold.threshold parameter)
        * sumBoxBadEnergy (boxes certificate)
      ≡ sumBoxBadEnergy (boxes certificate)
    leftCancel =
      trans
        (cong
          (_* sumBoxBadEnergy (boxes certificate))
          (Threshold.inverseMeaning parameter))
        (solve (sumBoxBadEnergy (boxes certificate) ∷ []))

    leftMeaning = trans leftRegroup leftCancel
  in
  subst
    (λ lower →
      lower ≤ Threshold.thresholdInverse parameter * packingEnvelope certificate)
    leftMeaning
    scaled

packedGoodSquaresBelowThresholdEnvelope :
  ∀ {parameter goodCoefficient} →
  (certificate : DirectionalDefectPackingCertificate
    parameter goodCoefficient) →
  sumGoodProductionSquare (boxes certificate)
  ≤ goodCoefficient * Threshold.threshold parameter
      * packingEnvelope certificate
packedGoodSquaresBelowThresholdEnvelope
    {parameter} {goodCoefficient} certificate =
  let
    first = sumGoodSquaresBelowGoodDefect
      (goodCoefficientNonnegative certificate)
      (boxes certificate)

    scale = goodCoefficient * Threshold.threshold parameter
    scaleNN =
      let
        instance
          coefficientNN = nonNegative (goodCoefficientNonnegative certificate)
          thresholdNN = nonNegative (Threshold.thresholdNonnegative parameter)
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg
            goodCoefficient (Threshold.threshold parameter)
      in
      ℚP.nonNegative⁻¹ scale

    goodToTotal :
      scale * sumBoxGoodDefect (boxes certificate)
      ≤ scale * sumBoxDefect (boxes certificate)
    goodToTotal =
      let instance scaleNNI = nonNegative scaleNN
      in ℚP.*-monoˡ-≤-nonNeg scale
        (sumGoodDefectBelowTotalDefect (boxes certificate))

    totalToEnvelope :
      scale * sumBoxDefect (boxes certificate)
      ≤ scale * packingEnvelope certificate
    totalToEnvelope =
      let instance scaleNNI = nonNegative scaleNN
      in ℚP.*-monoˡ-≤-nonNeg scale (defectPackingBound certificate)
  in
  ℚP.≤-trans first (ℚP.≤-trans goodToTotal totalToEnvelope)

hhDirectionalDefectPackingReductionClosed : Bool
hhDirectionalDefectPackingReductionClosed = true

onePackingEstimateFeedsBothHHStrata : Bool
onePackingEstimateFeedsBothHHStrata = true

physicalShellTimeDirectionalDefectPackingConstructed : Bool
physicalShellTimeDirectionalDefectPackingConstructed = false

hhDirectionalDefectPackingReductionClosedIsTrue :
  hhDirectionalDefectPackingReductionClosed ≡ true
hhDirectionalDefectPackingReductionClosedIsTrue = refl

onePackingEstimateFeedsBothHHStrataIsTrue :
  onePackingEstimateFeedsBothHHStrata ≡ true
onePackingEstimateFeedsBothHHStrataIsTrue = refl
