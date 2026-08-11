module DASHI.Physics.Closure.NSTriadKNHHUnifiedDirectionalDefectRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 38/39 treated HH-good depletion and HH-bad restricted dissipation as
-- operationally distinct lanes.  They are nevertheless complementary strata
-- of the same directional defect
--
--   Theta = 1 - (xi . eta)^2 = |xi x eta|^2.
--
-- On a bad cell, delta <= Theta.  Therefore, for every nonnegative energy E,
--
--   delta E <= E Theta.
--
-- This is the division-free form of 1_{Theta>delta} <= Theta/delta.  Summing
-- gives a single weighted-defect measure which controls bad occupation, while
-- the existing HH-good theorem uses Theta <= delta on the complementary
-- stratum.  No time derivative of the classifier is introduced.
--
-- The same theorem is also transported through an arbitrary nonnegative
-- shell/viscosity factor:
--
--   delta * (factor * badEnergy)
--     <= factor * weightedDirectionalDefect.
--
-- Thus the bad viscous charge can be dominated by the same E*Theta measure
-- once the physical factor is supplied.  The remaining frontier is the PDE
-- estimate on the physical time-integrated weighted defect itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Markov
import DASHI.Physics.Closure.NSTriadKNHHGoodPhysicalThresholdStretchingRound38Exact as Good

record PhysicalBadDirectionalEnergyCell
    (parameter : Markov.PositiveThreshold) : Set where
  constructor physical-bad-directional-energy-cell
  field
    pair : Physical.PhysicalVorticityPair
    energy : ℚ
    energyNonnegative : 0ℚ ≤ energy
    badThreshold :
      Markov.threshold parameter
      ≤ Gram.directionalDefect (Physical.directions pair)

open PhysicalBadDirectionalEnergyCell public

toMarkovCell :
  ∀ {parameter} →
  PhysicalBadDirectionalEnergyCell parameter →
  Markov.BadCoherenceCell parameter
toMarkovCell {parameter} cell =
  Markov.bad-coherence-cell
    (energy cell)
    (Gram.directionalDefect (Physical.directions (pair cell)))
    (energyNonnegative cell)
    (Gram.directionalDefectNonnegative (Physical.directions (pair cell)))
    (badThreshold cell)

mapBadCells :
  ∀ {parameter} →
  List (PhysicalBadDirectionalEnergyCell parameter) →
  List (Markov.BadCoherenceCell parameter)
mapBadCells [] = []
mapBadCells (cell ∷ rest) = toMarkovCell cell ∷ mapBadCells rest

badEnergyMass :
  ∀ {parameter} →
  List (PhysicalBadDirectionalEnergyCell parameter) → ℚ
badEnergyMass {parameter} cells =
  Markov.badWeightMass parameter (mapBadCells cells)

weightedDirectionalDefectMass :
  ∀ {parameter} →
  List (PhysicalBadDirectionalEnergyCell parameter) → ℚ
weightedDirectionalDefectMass {parameter} cells =
  Markov.weightedDefectMass parameter (mapBadCells cells)

badEnergyNonnegative :
  ∀ {parameter}
    (cells : List (PhysicalBadDirectionalEnergyCell parameter)) →
  0ℚ ≤ badEnergyMass cells
badEnergyNonnegative {parameter} cells =
  Markov.badWeightMassNonnegative parameter (mapBadCells cells)

weightedDirectionalDefectMassNonnegative :
  ∀ {parameter}
    (cells : List (PhysicalBadDirectionalEnergyCell parameter)) →
  0ℚ ≤ weightedDirectionalDefectMass cells
weightedDirectionalDefectMassNonnegative {parameter} cells =
  Markov.weightedDefectMassNonnegative parameter (mapBadCells cells)

thresholdTimesBadEnergyBelowDirectionalDefect :
  ∀ {parameter}
    (cells : List (PhysicalBadDirectionalEnergyCell parameter)) →
  Markov.threshold parameter * badEnergyMass cells
  ≤ weightedDirectionalDefectMass cells
thresholdTimesBadEnergyBelowDirectionalDefect {parameter} cells =
  Markov.thresholdTimesBadWeightBelowDefect parameter (mapBadCells cells)

------------------------------------------------------------------------
-- The same defect mass controls every nonnegative scaled bad charge.
------------------------------------------------------------------------

scaledBadCharge :
  ∀ {parameter} →
  ℚ → List (PhysicalBadDirectionalEnergyCell parameter) → ℚ
scaledBadCharge factor cells = factor * badEnergyMass cells

scaledDefectCharge :
  ∀ {parameter} →
  ℚ → List (PhysicalBadDirectionalEnergyCell parameter) → ℚ
scaledDefectCharge factor cells = factor * weightedDirectionalDefectMass cells

thresholdTimesScaledBadChargeBelowScaledDefect :
  ∀ {parameter}
    (factor : ℚ) →
    0ℚ ≤ factor →
    (cells : List (PhysicalBadDirectionalEnergyCell parameter)) →
  Markov.threshold parameter * scaledBadCharge factor cells
  ≤ scaledDefectCharge factor cells
thresholdTimesScaledBadChargeBelowScaledDefect
    {parameter} factor factorNN cells =
  let
    base :
      Markov.threshold parameter * badEnergyMass cells
      ≤ weightedDirectionalDefectMass cells
    base = thresholdTimesBadEnergyBelowDirectionalDefect cells

    scaled :
      factor * (Markov.threshold parameter * badEnergyMass cells)
      ≤ factor * weightedDirectionalDefectMass cells
    scaled =
      let instance factorNNI = Data.Rational.Base.nonNegative factorNN
      in ℚP.*-monoˡ-≤-nonNeg factor base

    leftMeaning :
      factor * (Markov.threshold parameter * badEnergyMass cells)
      ≡ Markov.threshold parameter * scaledBadCharge factor cells
    leftMeaning = solve
      ( factor
      ∷ Markov.threshold parameter
      ∷ badEnergyMass cells
      ∷ [])
  in
  subst
    (λ lower → lower ≤ scaledDefectCharge factor cells)
    leftMeaning
    scaled

------------------------------------------------------------------------
-- Physical cross-product interpretation of the defect density.
------------------------------------------------------------------------

physicalDefectDensity :
  ℚ → Physical.PhysicalVorticityPair → ℚ
physicalDefectDensity energyWeight physicalPair =
  energyWeight
    * L2.square (Physical.leftAmplitude physicalPair)
    * L2.square (Physical.rightAmplitude physicalPair)
    * Gram.directionalDefect (Physical.directions physicalPair)

physicalCrossResidualDensity :
  ℚ → Physical.PhysicalVorticityPair → ℚ
physicalCrossResidualDensity energyWeight physicalPair =
  energyWeight
    * Gram.crossNormSquared
        (Physical.leftVorticity physicalPair)
        (Physical.rightVorticity physicalPair)

physicalCrossResidualDensityEqualsDefectDensity :
  ∀ energyWeight physicalPair →
  physicalCrossResidualDensity energyWeight physicalPair
  ≡ physicalDefectDensity energyWeight physicalPair
physicalCrossResidualDensityEqualsDefectDensity energyWeight physicalPair =
  Physical.weightedPhysicalDirectionalDefectIdentity
    energyWeight physicalPair

------------------------------------------------------------------------
-- A single package exposes the complementary good/bad uses of Theta.
------------------------------------------------------------------------

record UnifiedHighHighDirectionalSplit
    (parameter : Markov.PositiveThreshold) : Set where
  field
    goodPair : Good.PhysicalHHGoodPair parameter
    badCells : List (PhysicalBadDirectionalEnergyCell parameter)

open UnifiedHighHighDirectionalSplit public

goodDefectBelowThreshold :
  ∀ {parameter}
    (split : UnifiedHighHighDirectionalSplit parameter) →
  Gram.directionalDefect
    (Physical.directions (Good.pair (goodPair split)))
  ≤ Markov.threshold parameter
goodDefectBelowThreshold split = Good.goodThreshold (goodPair split)

badMassControlledBySameDefect :
  ∀ {parameter}
    (split : UnifiedHighHighDirectionalSplit parameter) →
  Markov.threshold parameter * badEnergyMass (badCells split)
  ≤ weightedDirectionalDefectMass (badCells split)
badMassControlledBySameDefect split =
  thresholdTimesBadEnergyBelowDirectionalDefect (badCells split)

hhUnifiedDirectionalDefectClosed : Bool
hhUnifiedDirectionalDefectClosed = true

physicalTimeIntegratedDirectionalDefectEstimateConstructed : Bool
physicalTimeIntegratedDirectionalDefectEstimateConstructed = false

hhUnifiedDirectionalDefectClosedIsTrue :
  hhUnifiedDirectionalDefectClosed ≡ true
hhUnifiedDirectionalDefectClosedIsTrue = refl
