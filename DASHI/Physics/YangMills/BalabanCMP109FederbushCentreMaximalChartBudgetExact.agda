module DASHI.Physics.YangMills.BalabanCMP109FederbushCentreMaximalChartBudgetExact where

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
-- DASHI CONTRIBUTION
--
-- Use the FULL remaining CMP98 pre-log budget for the Federbush centre.
-- The selected contour is already certified at
--
--      ||U_j R^-1-I||_op <= 3/256.
--
-- Since the source threshold is 1/24, the centre need only satisfy
--
--      ||R V^-1-I||_op <= 1/24 - 3/256 = 23/768,
--
-- not the unnecessarily strong 3/256 bound used by the first Round-51
-- invariant-ball formulation.  The exact identity
--
--      3/256 + 23/768 = 1/24
--
-- then closes the relative defect and CMP98 equation-(25) gives
-- ||log(U_j V^-1)||_op <= 1/12.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact as Eq38
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreRelativeChartExact as Centre
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope

centreMaximalAllowance : ℚ
centreMaximalAllowance = Chart.sourceDefectThreshold - Budget.length24OperatorDefectBudget

centreMaximalAllowanceIsTwentyThree768 :
  centreMaximalAllowance ≡ + 23 / 768
centreMaximalAllowanceIsTwentyThree768 = ℚRing.solve []

contourPlusMaximalCentreIsThreshold :
  Budget.length24OperatorDefectBudget + centreMaximalAllowance
  ≡ Chart.sourceDefectThreshold
contourPlusMaximalCentreIsThreshold = ℚRing.solve []

centreMaximalAllowanceNonnegative : 0ℚ ≤ centreMaximalAllowance
centreMaximalAllowanceNonnegative = ℚP.nonNegative⁻¹ centreMaximalAllowance

record MaximalCentreChartBall
    {Unitary : Set}
    (group : Centre.UnitaryDefectGroup Unitary)
    (input reference centre : Unitary) : Set where
  field
    inputInsideSelectedContourRadius :
      Telescope.defect (Centre.kernel group)
        (Centre.relative group input reference)
      ≤ Budget.length24OperatorDefectBudget

    centreInsideMaximalAllowance :
      Telescope.defect (Centre.kernel group)
        (Centre.relative group reference centre)
      ≤ centreMaximalAllowance

open MaximalCentreChartBall public

maximalCentreBallImpliesRelativeSourceThreshold :
  ∀ {Unitary} (group : Centre.UnitaryDefectGroup Unitary)
    input reference centre →
  MaximalCentreChartBall group input reference centre →
  Telescope.defect (Centre.kernel group)
    (Centre.relative group input centre)
  ≤ Chart.sourceDefectThreshold
maximalCentreBallImpliesRelativeSourceThreshold group input reference centre bounds =
  let
    pairBound :
      Telescope.defect (Centre.kernel group)
        (Centre.relative group input reference)
      + Telescope.defect (Centre.kernel group)
        (Centre.relative group reference centre)
      ≤ Budget.length24OperatorDefectBudget + centreMaximalAllowance
    pairBound = ℚP.+-mono-≤
      (inputInsideSelectedContourRadius bounds)
      (centreInsideMaximalAllowance bounds)

    pairBelowThreshold :
      Telescope.defect (Centre.kernel group)
        (Centre.relative group input reference)
      + Telescope.defect (Centre.kernel group)
        (Centre.relative group reference centre)
      ≤ Chart.sourceDefectThreshold
    pairBelowThreshold =
      subst
        (λ upper →
          Telescope.defect (Centre.kernel group)
            (Centre.relative group input reference)
          + Telescope.defect (Centre.kernel group)
            (Centre.relative group reference centre)
          ≤ upper)
        contourPlusMaximalCentreIsThreshold
        pairBound
  in
  ℚP.≤-trans
    (Centre.relativeDefectTriangleThroughReference group input reference centre)
    pairBelowThreshold

maximalCentreBallImpliesSourceYRadius :
  ∀ {Unitary} (group : Centre.UnitaryDefectGroup Unitary)
    input reference centre logMagnitude →
  MaximalCentreChartBall group input reference centre →
  Chart.PrincipalLogDefectBound
    (Telescope.defect (Centre.kernel group)
      (Centre.relative group input centre))
    logMagnitude →
  logMagnitude ≤ Eq38.sourceYRadius
maximalCentreBallImpliesSourceYRadius
    group input reference centre logMagnitude ball logBound =
  Chart.defectOneTwentyFourthImpliesYRadius
    (Telescope.defect (Centre.kernel group)
      (Centre.relative group input centre))
    logMagnitude
    logBound
    (maximalCentreBallImpliesRelativeSourceThreshold
      group input reference centre ball)

cmp109FederbushMaximalCentreChartBudgetLevel : ProofLevel
cmp109FederbushMaximalCentreChartBudgetLevel = machineChecked

-- The physical centre theorem now has 23/768 of operator-defect radius, more
-- than 2.5 times the already-certified 3/256 contour radius.
cmp109FederbushPhysicalCentreMaximalAllowanceLevel : ProofLevel
cmp109FederbushPhysicalCentreMaximalAllowanceLevel = conditional
