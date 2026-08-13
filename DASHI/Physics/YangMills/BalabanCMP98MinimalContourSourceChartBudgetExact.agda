module DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact where

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
-- Combine the repository's already-proved minimal CMP109 contour length 24
-- with the configured P33 radius rho=1/8192.  If each literal SU(2) path step
-- has operator defect at most 2 rho = 1/4096, then a length-24 contour has
-- total telescoping defect at most
--
--       24 / 4096 = 3/512 < 1/24.
--
-- By Bałaban CMP98 equation (25), rationalized as |log U| <= 2 |U-1|,
-- this is more than enough for equation (38)'s |Y| <= 1/12 source chart.
--
-- Thus G1's Y-radius is no longer a mysterious analytic constant problem: on
-- the minimal source geometry it reduces exactly to the local physical
-- operator-defect/telescoping identification for each selected contour factor.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_≤_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33CMP109MinimalPathStageBudgetExact as PathBudget
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact as Eq38

perLinkOperatorDefectBudget : ℚ
perLinkOperatorDefectBudget = (+ 2 / 1) * P33.p33SmallFieldRadius

length24OperatorDefectBudget : ℚ
length24OperatorDefectBudget = (+ 24 / 1) * perLinkOperatorDefectBudget

perLinkOperatorDefectIsOne4096 :
  perLinkOperatorDefectBudget ≡ + 1 / 4096
perLinkOperatorDefectIsOne4096 = ℚRing.solve []

length24OperatorDefectIsThree512 :
  length24OperatorDefectBudget ≡ + 3 / 512
length24OperatorDefectIsThree512 = ℚRing.solve []

length24DefectStrictlyInsideSourceThreshold :
  length24OperatorDefectBudget < Chart.sourceDefectThreshold
length24DefectStrictlyInsideSourceThreshold =
  ℚP.positive⁻¹
    (Chart.sourceDefectThreshold - length24OperatorDefectBudget)

length24DefectInsideSourceThreshold :
  length24OperatorDefectBudget ≤ Chart.sourceDefectThreshold
length24DefectInsideSourceThreshold =
  ℚP.<⇒≤ length24DefectStrictlyInsideSourceThreshold

perLinkOperatorDefectNonnegative : 0ℚ ≤ perLinkOperatorDefectBudget
perLinkOperatorDefectNonnegative = ℚP.nonNegative⁻¹ perLinkOperatorDefectBudget

finiteLength24DefectSum :
  ∀ {A : Set}
    (values : List A) →
  PathBudget.Periodic.listLength values ≤ 24 →
  (defect : A → ℚ) →
  (∀ value → defect value ≤ perLinkOperatorDefectBudget) →
  Sums.sumRational values defect ≤ length24OperatorDefectBudget
finiteLength24DefectSum values lengthBound defect pointwise =
  subst
    (λ upper → Sums.sumRational values defect ≤ upper)
    (ℚRing.solve [] :
      Sums.natAsRational 24 * perLinkOperatorDefectBudget
      ≡ length24OperatorDefectBudget)
    (PathBudget.finiteUniformSumBoundByLength
      values 24 defect perLinkOperatorDefectBudget
      perLinkOperatorDefectNonnegative lengthBound pointwise)

length24TelescopingDefectImpliesSourceYRadius :
  ∀ contourDefect logMagnitude →
  contourDefect ≤ length24OperatorDefectBudget →
  Chart.PrincipalLogDefectBound contourDefect logMagnitude →
  logMagnitude ≤ Eq38.sourceYRadius
length24TelescopingDefectImpliesSourceYRadius
    contourDefect logMagnitude contourBound logBound =
  Chart.defectOneTwentyFourthImpliesYRadius
    contourDefect logMagnitude logBound
    (ℚP.≤-trans contourBound length24DefectInsideSourceThreshold)

cmp98MinimalContourDefectBudgetLevel : ProofLevel
cmp98MinimalContourDefectBudgetLevel = machineChecked

cmp98MinimalContourYRadiusArithmeticLevel : ProofLevel
cmp98MinimalContourYRadiusArithmeticLevel = machineChecked
