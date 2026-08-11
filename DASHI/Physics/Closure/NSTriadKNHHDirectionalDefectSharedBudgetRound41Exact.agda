module DASHI.Physics.Closure.NSTriadKNHHDirectionalDefectSharedBudgetRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 40 showed that HH-good depletion and HH-bad occupation are
-- complementary strata of the same directional defect
--
--   Theta = 1 - (xi . eta)^2.
--
-- Round 41 now puts both strata on one *full classified measure*, rather than
-- calling the bad restriction itself the common measure.  Every physical cell
-- owns one vorticity pair, one nonnegative energy weight, one good/bad tag and
-- evidence for the corresponding threshold inequality.  From those same
-- cells we define
--
--   D_dir       = sum_all E_i Theta_i,
--   D_dir^good  = sum_good E_i Theta_i,
--   D_dir^bad   = sum_bad E_i Theta_i,
--   E_bad       = sum_bad E_i.
--
-- and prove exactly
--
--   D_dir = D_dir^good + D_dir^bad,
--   delta E_bad <= D_dir^bad <= D_dir.
--
-- Therefore one physical time-integrated estimate
--
--   D_dir <= alpha D + A + B X
--
-- controls bad occupation while the good stratum remains an exact component
-- of the same measure.  No differentiated classifier and no independently
-- selected bad occupation measure is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner

data DirectionalRegion : Set where
  goodRegion badRegion : DirectionalRegion

RegionEvidence :
  Threshold.PositiveThreshold →
  Physical.PhysicalVorticityPair →
  DirectionalRegion → Set
RegionEvidence parameter pair goodRegion =
  Gram.directionalDefect (Physical.directions pair)
  ≤ Threshold.threshold parameter
RegionEvidence parameter pair badRegion =
  Threshold.threshold parameter
  ≤ Gram.directionalDefect (Physical.directions pair)

record ClassifiedDirectionalEnergyCell
    (parameter : Threshold.PositiveThreshold) : Set where
  constructor classified-directional-energy-cell
  field
    pair : Physical.PhysicalVorticityPair
    energy : ℚ
    energyNonnegative : 0ℚ ≤ energy
    region : DirectionalRegion
    regionEvidence : RegionEvidence parameter pair region

open ClassifiedDirectionalEnergyCell public

cellDefect :
  ∀ {parameter} → ClassifiedDirectionalEnergyCell parameter → ℚ
cellDefect cell =
  energy cell * Gram.directionalDefect (Physical.directions (pair cell))

badEnergyContribution :
  ∀ {parameter} → ClassifiedDirectionalEnergyCell parameter → ℚ
badEnergyContribution cell with region cell
... | goodRegion = 0ℚ
... | badRegion = energy cell

badDefectContribution :
  ∀ {parameter} → ClassifiedDirectionalEnergyCell parameter → ℚ
badDefectContribution cell with region cell
... | goodRegion = 0ℚ
... | badRegion = cellDefect cell

goodDefectContribution :
  ∀ {parameter} → ClassifiedDirectionalEnergyCell parameter → ℚ
goodDefectContribution cell with region cell
... | goodRegion = cellDefect cell
... | badRegion = 0ℚ

cellDefectNonnegative :
  ∀ {parameter} (cell : ClassifiedDirectionalEnergyCell parameter) →
  0ℚ ≤ cellDefect cell
cellDefectNonnegative cell =
  let
    thetaNN = Gram.directionalDefectNonnegative
      (Physical.directions (pair cell))
    instance
      energyNNI = nonNegative (energyNonnegative cell)
      thetaNNI = nonNegative thetaNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
        (energy cell)
        (Gram.directionalDefect (Physical.directions (pair cell)))
  in
  ℚP.nonNegative⁻¹ (cellDefect cell)

badDefectContributionBelowCellDefect :
  ∀ {parameter} (cell : ClassifiedDirectionalEnergyCell parameter) →
  badDefectContribution cell ≤ cellDefect cell
badDefectContributionBelowCellDefect cell with region cell
... | goodRegion = cellDefectNonnegative cell
... | badRegion = ℚP.≤-refl

thresholdTimesBadEnergyContributionBelowBadDefect :
  ∀ {parameter} (cell : ClassifiedDirectionalEnergyCell parameter) →
  Threshold.threshold parameter * badEnergyContribution cell
  ≤ badDefectContribution cell
thresholdTimesBadEnergyContributionBelowBadDefect
    {parameter} cell with region cell
... | goodRegion =
  subst
    (λ right → 0ℚ ≤ right)
    (sym (solve []))
    ℚP.≤-refl
... | badRegion =
  let
    evidence = regionEvidence cell
    scaled :
      energy cell * Threshold.threshold parameter
      ≤ energy cell * Gram.directionalDefect (Physical.directions (pair cell))
    scaled =
      let instance energyNNI = nonNegative (energyNonnegative cell)
      in ℚP.*-monoˡ-≤-nonNeg (energy cell) evidence

    leftMeaning :
      energy cell * Threshold.threshold parameter
      ≡ Threshold.threshold parameter * energy cell
    leftMeaning = solve (energy cell ∷ Threshold.threshold parameter ∷ [])
  in
  subst
    (λ lower → lower ≤ cellDefect cell)
    leftMeaning
    scaled

totalDirectionalDefectMass :
  ∀ {parameter} → List (ClassifiedDirectionalEnergyCell parameter) → ℚ
totalDirectionalDefectMass [] = 0ℚ
totalDirectionalDefectMass (cell ∷ rest) =
  cellDefect cell + totalDirectionalDefectMass rest

badDirectionalDefectMass :
  ∀ {parameter} → List (ClassifiedDirectionalEnergyCell parameter) → ℚ
badDirectionalDefectMass [] = 0ℚ
badDirectionalDefectMass (cell ∷ rest) =
  badDefectContribution cell + badDirectionalDefectMass rest

goodDirectionalDefectMass :
  ∀ {parameter} → List (ClassifiedDirectionalEnergyCell parameter) → ℚ
goodDirectionalDefectMass [] = 0ℚ
goodDirectionalDefectMass (cell ∷ rest) =
  goodDefectContribution cell + goodDirectionalDefectMass rest

badEnergyMass :
  ∀ {parameter} → List (ClassifiedDirectionalEnergyCell parameter) → ℚ
badEnergyMass [] = 0ℚ
badEnergyMass (cell ∷ rest) =
  badEnergyContribution cell + badEnergyMass rest

classifiedDefectSplitsGoodBad :
  ∀ {parameter}
    (cells : List (ClassifiedDirectionalEnergyCell parameter)) →
  totalDirectionalDefectMass cells
  ≡ goodDirectionalDefectMass cells + badDirectionalDefectMass cells
classifiedDefectSplitsGoodBad [] = solve []
classifiedDefectSplitsGoodBad (cell ∷ rest) with region cell
... | goodRegion
  rewrite classifiedDefectSplitsGoodBad rest =
  solve
    ( cellDefect cell
    ∷ goodDirectionalDefectMass rest
    ∷ badDirectionalDefectMass rest
    ∷ [])
... | badRegion
  rewrite classifiedDefectSplitsGoodBad rest =
  solve
    ( cellDefect cell
    ∷ goodDirectionalDefectMass rest
    ∷ badDirectionalDefectMass rest
    ∷ [])

badDefectMassBelowTotalDefect :
  ∀ {parameter}
    (cells : List (ClassifiedDirectionalEnergyCell parameter)) →
  badDirectionalDefectMass cells ≤ totalDirectionalDefectMass cells
badDefectMassBelowTotalDefect [] = ℚP.≤-refl
badDefectMassBelowTotalDefect (cell ∷ rest) =
  ℚP.+-mono-≤
    (badDefectContributionBelowCellDefect cell)
    (badDefectMassBelowTotalDefect rest)

thresholdTimesBadEnergyBelowBadDefect :
  ∀ {parameter}
    (cells : List (ClassifiedDirectionalEnergyCell parameter)) →
  Threshold.threshold parameter * badEnergyMass cells
  ≤ badDirectionalDefectMass cells
thresholdTimesBadEnergyBelowBadDefect {parameter} [] =
  subst (λ left → left ≤ 0ℚ)
    (solve (Threshold.threshold parameter ∷ []))
    ℚP.≤-refl
thresholdTimesBadEnergyBelowBadDefect {parameter} (cell ∷ rest) =
  let
    local = thresholdTimesBadEnergyContributionBelowBadDefect cell
    tail = thresholdTimesBadEnergyBelowBadDefect rest
    added = ℚP.+-mono-≤ local tail

    leftMeaning :
      Threshold.threshold parameter
        * (badEnergyContribution cell + badEnergyMass rest)
      ≡
      Threshold.threshold parameter * badEnergyContribution cell
      + Threshold.threshold parameter * badEnergyMass rest
    leftMeaning = solve
      ( Threshold.threshold parameter
      ∷ badEnergyContribution cell
      ∷ badEnergyMass rest
      ∷ [])
  in
  subst
    (λ lower → lower ≤ badDirectionalDefectMass (cell ∷ rest))
    (sym leftMeaning)
    added

thresholdTimesBadEnergyBelowTotalDefect :
  ∀ {parameter}
    (cells : List (ClassifiedDirectionalEnergyCell parameter)) →
  Threshold.threshold parameter * badEnergyMass cells
  ≤ totalDirectionalDefectMass cells
thresholdTimesBadEnergyBelowTotalDefect cells =
  ℚP.≤-trans
    (thresholdTimesBadEnergyBelowBadDefect cells)
    (badDefectMassBelowTotalDefect cells)

record PhysicalDirectionalDefectBudget
    (environment : Owner.TaxEnvironment)
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    cells : List (ClassifiedDirectionalEnergyCell parameter)
    eta dataRemainder criticalCoefficient : ℚ

    etaNonnegative : 0ℚ ≤ eta
    dataRemainderNonnegative : 0ℚ ≤ dataRemainder
    criticalCoefficientNonnegative : 0ℚ ≤ criticalCoefficient
    dissipationNonnegative : 0ℚ ≤ Owner.dissipation environment
    integralCriticalNonnegative : 0ℚ ≤ Owner.integralCritical environment

    timeIntegratedDirectionalDefectBound :
      totalDirectionalDefectMass cells
      ≤ eta * Owner.dissipation environment
        + dataRemainder
        + criticalCoefficient * Owner.integralCritical environment

open PhysicalDirectionalDefectBudget public

defectBudgetRight :
  ∀ {environment parameter} →
  PhysicalDirectionalDefectBudget environment parameter → ℚ
defectBudgetRight {environment} budget =
  eta budget * Owner.dissipation environment
  + dataRemainder budget
  + criticalCoefficient budget * Owner.integralCritical environment

thresholdBadEnergyBelowSharedBudget :
  ∀ {environment parameter}
    (budget : PhysicalDirectionalDefectBudget environment parameter) →
  Threshold.threshold parameter * badEnergyMass (cells budget)
  ≤ defectBudgetRight budget
thresholdBadEnergyBelowSharedBudget budget =
  ℚP.≤-trans
    (thresholdTimesBadEnergyBelowTotalDefect (cells budget))
    (timeIntegratedDirectionalDefectBound budget)

record HHGoodUseOfDirectionalDefect
    {environment : Owner.TaxEnvironment}
    {parameter : Threshold.PositiveThreshold}
    (budget : PhysicalDirectionalDefectBudget environment parameter) : Set where
  field
    goodProductionSquare coefficient : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient
    goodProductionSquareNonnegative : 0ℚ ≤ goodProductionSquare
    goodSquareBelowDefect :
      goodProductionSquare
      ≤ coefficient * Threshold.threshold parameter
          * goodDirectionalDefectMass (cells budget)

open HHGoodUseOfDirectionalDefect public

goodDefectMassBelowTotalDefect :
  ∀ {parameter}
    (cells : List (ClassifiedDirectionalEnergyCell parameter)) →
  goodDirectionalDefectMass cells ≤ totalDirectionalDefectMass cells
goodDefectMassBelowTotalDefect [] = ℚP.≤-refl
goodDefectMassBelowTotalDefect (cell ∷ rest) with region cell
... | goodRegion =
  ℚP.+-mono-≤ ℚP.≤-refl (goodDefectMassBelowTotalDefect rest)
... | badRegion =
  ℚP.+-mono-≤ (cellDefectNonnegative cell)
    (goodDefectMassBelowTotalDefect rest)

goodSquareBelowScaledSharedBudget :
  ∀ {environment parameter}
    {budget : PhysicalDirectionalDefectBudget environment parameter} →
  (good : HHGoodUseOfDirectionalDefect budget) →
  goodProductionSquare good
  ≤ coefficient good * Threshold.threshold parameter
      * defectBudgetRight budget
goodSquareBelowScaledSharedBudget {parameter = parameter} {budget} good =
  let
    scale = coefficient good * Threshold.threshold parameter
    scaleNN : 0ℚ ≤ scale
    scaleNN =
      let
        instance
          coefficientNNI = nonNegative (coefficientNonnegative good)
          thresholdNNI = nonNegative (Threshold.thresholdNonnegative parameter)
          productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
            (coefficient good) (Threshold.threshold parameter)
      in
      ℚP.nonNegative⁻¹ scale

    goodToTotal :
      scale * goodDirectionalDefectMass (cells budget)
      ≤ scale * totalDirectionalDefectMass (cells budget)
    goodToTotal =
      let instance scaleNNI = nonNegative scaleNN
      in ℚP.*-monoˡ-≤-nonNeg scale
        (goodDefectMassBelowTotalDefect (cells budget))

    totalToBudget :
      scale * totalDirectionalDefectMass (cells budget)
      ≤ scale * defectBudgetRight budget
    totalToBudget =
      let instance scaleNNI = nonNegative scaleNN
      in ℚP.*-monoˡ-≤-nonNeg scale
        (timeIntegratedDirectionalDefectBound budget)

    first :
      goodProductionSquare good
      ≤ scale * goodDirectionalDefectMass (cells budget)
    first = goodSquareBelowDefect good
  in
  ℚP.≤-trans first (ℚP.≤-trans goodToTotal totalToBudget)

sharedDirectionalDefectBudgetClosed : Bool
sharedDirectionalDefectBudgetClosed = true

classifiedDirectionalDefectPartitionClosed : Bool
classifiedDirectionalDefectPartitionClosed = true

physicalTimeIntegratedDirectionalDefectBudgetConstructed : Bool
physicalTimeIntegratedDirectionalDefectBudgetConstructed = false

sharedDirectionalDefectBudgetClosedIsTrue :
  sharedDirectionalDefectBudgetClosed ≡ true
sharedDirectionalDefectBudgetClosedIsTrue = refl

classifiedDirectionalDefectPartitionClosedIsTrue :
  classifiedDirectionalDefectPartitionClosed ≡ true
classifiedDirectionalDefectPartitionClosedIsTrue = refl
