module DASHI.Physics.YangMills.BalabanP33WilsonDiagonalBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- The four explicit diagonal plaquette placements have already been reduced to
--
--   -q0(D_j S_j P_j),  j = 0,1,2,3.
--
-- This module fixes the non-overlapping quantitative allocation used by the
-- physical second-exponential-chart estimate.  A local bound rho/16 on each
-- chart remainder gives rho/4 for all four diagonal atoms.  Together with the
-- rho/2 six-pair cross allocation, the complete sixteen-atom Wilson remainder
-- consumes only 3 rho/4, retaining rho/4 of explicit scalar slack.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

data WilsonDiagonalSlot4 : Set where
  diagonal0 diagonal1 diagonal2 diagonal3 : WilsonDiagonalSlot4

wilsonDiagonalSlots4 : List WilsonDiagonalSlot4
wilsonDiagonalSlots4 =
  diagonal0 ∷ diagonal1 ∷ diagonal2 ∷ diagonal3 ∷ []

wilsonDiagonalCountExact : length wilsonDiagonalSlots4 ≡ 4
wilsonDiagonalCountExact = refl

p33Radius : ℚ
p33Radius = + 1 / 8192

localDiagonalChartAllocation : ℚ
localDiagonalChartAllocation = p33Radius * (+ 1 / 16)

completeDiagonalChartBudget : ℚ
completeDiagonalChartBudget = (+ 4 / 1) * localDiagonalChartAllocation

completeDiagonalChartBudgetIsQuarterRadius :
  completeDiagonalChartBudget ≡ p33Radius * (+ 1 / 4)
completeDiagonalChartBudgetIsQuarterRadius = ℚRing.solve []

completeCrossBudget : ℚ
completeCrossBudget = p33Radius * (+ 1 / 2)

completeSixteenAtomWilsonBudget : ℚ
completeSixteenAtomWilsonBudget =
  completeCrossBudget + completeDiagonalChartBudget

completeWilsonBudgetIsThreeQuarterRadius :
  completeSixteenAtomWilsonBudget ≡ p33Radius * (+ 3 / 4)
completeWilsonBudgetIsThreeQuarterRadius = ℚRing.solve []

remainingWilsonSlack : ℚ
remainingWilsonSlack = p33Radius * (+ 1 / 4)

completeWilsonBudgetPlusSlackIsRadius :
  completeSixteenAtomWilsonBudget + remainingWilsonSlack ≡ p33Radius
completeWilsonBudgetPlusSlackIsRadius = ℚRing.solve []

wilsonDiagonalPlacementLevel : ProofLevel
wilsonDiagonalPlacementLevel = machineChecked

wilsonDiagonalAllocationLevel : ProofLevel
wilsonDiagonalAllocationLevel = machineChecked

wilsonSixteenAtomSlackLevel : ProofLevel
wilsonSixteenAtomSlackLevel = machineChecked
