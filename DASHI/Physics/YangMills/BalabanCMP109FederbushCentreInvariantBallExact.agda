module DASHI.Physics.YangMills.BalabanCMP109FederbushCentreInvariantBallExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- DASHI CONTRIBUTION
--
-- Connect the repository's quantitative implicit-function/fixed-point theorem
-- directly to the final Federbush centre chart.  Once the physical equation-
-- (0.11) fixed-point map is proved to preserve the SAME 3/256 operator-defect
-- ball about a selected reference contour, the actual implicit solution V is
-- automatically in that ball.  Round 51's centre-relative theorem then gives
--
--   ||U_j V^-1-I||_op <= 3/128 < 1/24,
--
-- so the CMP98 Y-chart follows.
--
-- This removes "estimate the centre V" as an independent theorem.  The only
-- remaining G1 analytic producer is now the source-specific invariant-ball and
-- contraction estimate for the literal Federbush fixed-point map.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as QIF
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreRelativeChartExact as Centre

record FederbushInvariantBallRealization
    (Input Unitary : Set)
    (group : Centre.UnitaryDefectGroup Unitary)
    (dataSet : QIF.QuantitativeImplicitFunctionData Input Unitary ℚ)
    (input : Input)
    (reference : Unitary) : Set₁ where
  field
    admissible : QIF.AdmissibleInput dataSet input

    ballCentreIsReference :
      QIF.centre (QIF.contractionBall dataSet input) ≡ reference

    ballRadiusIsSelectedContourRadius :
      QIF.radius (QIF.contractionBall dataSet input)
      ≡ Budget.length24OperatorDefectBudget

    metricDistanceIsRelativeOperatorDefect : ∀ value →
      QIF.distance (QIF.metric dataSet) value reference
      ≡ Telescope.defect (Centre.kernel group)
          (Centre.relative group reference value)

open FederbushInvariantBallRealization public

federbushImplicitCentre :
  ∀ {Input Unitary group dataSet input reference} →
  FederbushInvariantBallRealization Input Unitary group dataSet input reference →
  Unitary
federbushImplicitCentre realization =
  QIF.implicitSolution _ _ (admissible realization)

implicitCentreInsideSelectedContourRadius :
  ∀ {Input Unitary group dataSet input reference}
    (realization : FederbushInvariantBallRealization
      Input Unitary group dataSet input reference) →
  Telescope.defect (Centre.kernel group)
    (Centre.relative group reference (federbushImplicitCentre realization))
  ≤ Budget.length24OperatorDefectBudget
implicitCentreInsideSelectedContourRadius
    {dataSet = dataSet} {input = input} {reference = reference}
    realization =
  let
    ball = QIF.contractionBall dataSet input
    centre = federbushImplicitCentre realization
    membership = QIF.implicitSolutionInBall dataSet input (admissible realization)

    distanceBound :
      QIF.LessEqual (QIF.metric dataSet)
        (QIF.distance (QIF.metric dataSet) centre (QIF.centre ball))
        (QIF.radius ball)
    distanceBound =
      subst
        (λ selected → selected)
        (QIF.inBallMeaning ball centre)
        membership

    referenceDistanceBound :
      QIF.LessEqual (QIF.metric dataSet)
        (QIF.distance (QIF.metric dataSet) centre reference)
        Budget.length24OperatorDefectBudget
    referenceDistanceBound =
      subst
        (λ selectedCentre →
          QIF.LessEqual (QIF.metric dataSet)
            (QIF.distance (QIF.metric dataSet) centre selectedCentre)
            Budget.length24OperatorDefectBudget)
        (ballCentreIsReference realization)
        (subst
          (λ selectedRadius →
            QIF.LessEqual (QIF.metric dataSet)
              (QIF.distance (QIF.metric dataSet) centre (QIF.centre ball))
              selectedRadius)
          (ballRadiusIsSelectedContourRadius realization)
          distanceBound)
  in
  subst
    (λ selected → selected ≤ Budget.length24OperatorDefectBudget)
    (metricDistanceIsRelativeOperatorDefect realization centre)
    referenceDistanceBound

cmp109FederbushCentreInvariantBallExtractionLevel : ProofLevel
cmp109FederbushCentreInvariantBallExtractionLevel = machineChecked

cmp109FederbushPhysicalInvariantBallAndContractionLevel : ProofLevel
cmp109FederbushPhysicalInvariantBallAndContractionLevel = conditional
