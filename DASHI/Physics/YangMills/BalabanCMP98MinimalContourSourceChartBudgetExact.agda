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
-- with the sharp square-root-free quaternion l1 defect derived from the
-- configured P33 radius.  Every physical link defect has l1 majorant 1/2048.
-- Since the SU(2) operator defect is bounded by that l1 quantity, a length-24
-- operator-norm telescope is bounded by
--
--       24 / 2048 = 3/256.
--
-- In particular a SINGLE selected contour is well inside the 1/24 pre-log
-- threshold.  More importantly, TWO such contour defects sum to
--
--       3/128 < 1/24,
--
-- so the same budget also accommodates a relative product U_j U_l^{-1} before
-- applying CMP98 equation (25).  This is the radius needed for the actual
-- Federbush relative logarithms.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_≤_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33CMP109MinimalPathStageBudgetExact as PathBudget
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact as Eq38
import DASHI.Physics.YangMills.BalabanP33RelaxedRadiusQuaternionL1SharpExact as RadiusL1

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

perLinkDefectMajorant : ℚ
perLinkDefectMajorant = RadiusL1.sharpL1Budget

length24OperatorDefectBudget : ℚ
length24OperatorDefectBudget = (+ 24 / 1) * perLinkDefectMajorant

relativeTwoContourDefectBudget : ℚ
relativeTwoContourDefectBudget =
  length24OperatorDefectBudget + length24OperatorDefectBudget

perLinkDefectMajorantIsOne2048 :
  perLinkDefectMajorant ≡ + 1 / 2048
perLinkDefectMajorantIsOne2048 = ℚRing.solve []

length24OperatorDefectIsThree256 :
  length24OperatorDefectBudget ≡ + 3 / 256
length24OperatorDefectIsThree256 = ℚRing.solve []

relativeTwoContourDefectIsThree128 :
  relativeTwoContourDefectBudget ≡ + 3 / 128
relativeTwoContourDefectIsThree128 = ℚRing.solve []

length24DefectInsideSourceThreshold :
  length24OperatorDefectBudget ≤ Chart.sourceDefectThreshold
length24DefectInsideSourceThreshold =
  ℚP.<⇒≤
    (ℚP.positive⁻¹
      (Chart.sourceDefectThreshold - length24OperatorDefectBudget))

relativeTwoContourDefectInsideSourceThreshold :
  relativeTwoContourDefectBudget ≤ Chart.sourceDefectThreshold
relativeTwoContourDefectInsideSourceThreshold =
  ℚP.<⇒≤
    (ℚP.positive⁻¹
      (Chart.sourceDefectThreshold - relativeTwoContourDefectBudget))

perLinkDefectMajorantNonnegative : 0ℚ ≤ perLinkDefectMajorant
perLinkDefectMajorantNonnegative = ℚP.nonNegative⁻¹ perLinkDefectMajorant

finiteLength24DefectSum :
  ∀ {A : Set}
    (values : List A) →
  listLength values ≤ 24 →
  (defectMajorant : A → ℚ) →
  (∀ value → defectMajorant value ≤ perLinkDefectMajorant) →
  Sums.sumRational values defectMajorant ≤ length24OperatorDefectBudget
finiteLength24DefectSum values lengthBound defectMajorant pointwise =
  subst
    (λ upper → Sums.sumRational values defectMajorant ≤ upper)
    (ℚRing.solve [] :
      Sums.natAsRational 24 * perLinkDefectMajorant
      ≡ length24OperatorDefectBudget)
    (PathBudget.finiteUniformSumBoundByLength
      values 24 defectMajorant perLinkDefectMajorant
      perLinkDefectMajorantNonnegative lengthBound pointwise)

length24TelescopingDefectImpliesSourceYRadius :
  ∀ contourOperatorDefect logMagnitude →
  contourOperatorDefect ≤ length24OperatorDefectBudget →
  Chart.PrincipalLogDefectBound contourOperatorDefect logMagnitude →
  logMagnitude ≤ Eq38.sourceYRadius
length24TelescopingDefectImpliesSourceYRadius
    contourOperatorDefect logMagnitude contourBound logBound =
  Chart.defectOneTwentyFourthImpliesYRadius
    contourOperatorDefect logMagnitude logBound
    (ℚP.≤-trans contourBound length24DefectInsideSourceThreshold)

relativeTwoContourDefectImpliesSourceYRadius :
  ∀ relativeOperatorDefect logMagnitude →
  relativeOperatorDefect ≤ relativeTwoContourDefectBudget →
  Chart.PrincipalLogDefectBound relativeOperatorDefect logMagnitude →
  logMagnitude ≤ Eq38.sourceYRadius
relativeTwoContourDefectImpliesSourceYRadius
    relativeOperatorDefect logMagnitude relativeBound logBound =
  Chart.defectOneTwentyFourthImpliesYRadius
    relativeOperatorDefect logMagnitude logBound
    (ℚP.≤-trans relativeBound
      relativeTwoContourDefectInsideSourceThreshold)

cmp98MinimalContourDefectBudgetLevel : ProofLevel
cmp98MinimalContourDefectBudgetLevel = machineChecked

cmp98MinimalContourRelativePairBudgetLevel : ProofLevel
cmp98MinimalContourRelativePairBudgetLevel = machineChecked

cmp98MinimalContourYRadiusArithmeticLevel : ProofLevel
cmp98MinimalContourYRadiusArithmeticLevel = machineChecked
