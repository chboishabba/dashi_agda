module DASHI.Biology.JCoarseFineBranchingCriticalityExact where

------------------------------------------------------------------------
-- SOURCE / PROVENANCE
--
-- This is a DASHI cross-pollination module.  Its motivating coarse/fine,
-- decimal-refinement, and branching interpretation comes from the supplied
-- DASHI discussion notes dated 2026-08-26.  The mathematical source roles are
-- deliberately separated:
--
-- Theodore E. Harris,
-- "The Theory of Branching Processes", Springer, 1963.
-- DOI: 10.1007/978-3-642-51866-9.
--
-- E. Seneta,
-- "Non-negative Matrices and Markov Chains", 2nd ed., Springer, 1981.
-- DOI: 10.1007/0-387-32792-4.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION / CLAIM BOUNDARY
--
-- The existing JCoarse/JFine owner supplies a pointed coarse/fine evaluation
-- and explicitly blocks the inference that every fixed fibre has size 3^9.
-- RecursiveFibreTower independently supplies a literal 27-code ternary level.
-- The new finite branching owner supplies only exact scaled arithmetic.
--
-- This file proves compatibility between those existing theorem surfaces.  It
-- does NOT identify JFine with a probability, assert statistical independence,
-- or claim that the accidental decimal equality 19.683 = 19683/1000 gives a
-- modular, biological, psychological, or physical interpretation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Biology.JCoarseFineEvaluationFibreExact as J
import DASHI.Biology.JFineCoarseRelativeScaleExact as Scale
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Core.DecimalResidualRefinementExact as Decimal
import DASHI.Core.FiniteBranchingCriticalityExact as Branch

------------------------------------------------------------------------
-- Existing ternary 27-code substrate reused directly.
------------------------------------------------------------------------

recursiveLevelTwoCodeCountIsTwentySeven :
  Tower.levelTwoCodeCount ≡ 27
recursiveLevelTwoCodeCountIsTwentySeven =
  Tower.levelTwoCodeCountIsTwentySeven

threeTernaryAxesCellCountMatchesRecursiveLevelTwo :
  Branch.jointAccessibleNumerator 3 3 1 ≡ Tower.levelTwoCodeCount
threeTernaryAxesCellCountMatchesRecursiveLevelTwo =
  trans Branch.threeTernaryAxesCellCount
        (sym Tower.levelTwoCodeCountIsTwentySeven)

------------------------------------------------------------------------
-- Critical reciprocal family.
------------------------------------------------------------------------

binaryHalfCritical : Branch.singleAxisRegime 2 1 2 ≡ Branch.critical
binaryHalfCritical = Branch.binaryHalfIsCritical

ternaryThirdCritical : Branch.singleAxisRegime 3 1 3 ≡ Branch.critical
ternaryThirdCritical = Branch.ternaryThirdIsCritical

quaternaryQuarterCritical : Branch.singleAxisRegime 4 1 4 ≡ Branch.critical
quaternaryQuarterCritical = Branch.quaternaryQuarterIsCritical

------------------------------------------------------------------------
-- The historical affine fixed point 5/18 is below ternary criticality.
--
-- The fixed-point equation and the branching classification are independent
-- theorem surfaces; composing them here records the exact retrospective fact
-- without asserting that the historical construction was originally derived
-- from branching-process theory.
------------------------------------------------------------------------

fiveEighteenthsSolvesHistoricalAffineEquation :
  Branch.affineQuarterTenthFixedPointEquation 5 18
fiveEighteenthsSolvesHistoricalAffineEquation =
  Branch.fiveEighteenthsSolvesAffineQuarterTenth

fiveEighteenthsIsTernarySubcritical :
  Branch.singleAxisRegime 3 5 18 ≡ Branch.subcritical
fiveEighteenthsIsTernarySubcritical =
  Branch.ternaryFiveEighteenthsIsSubcritical

------------------------------------------------------------------------
-- Exact 0.9 / three-axis arithmetic and JFine digit coincidence.
--
-- In the independent three-axis toy count:
--
--   (3 * 9)^3 / 10^3 = 19683 / 1000 = 19.683.
--
-- Existing DASHI independently has jFineFrequency = 19683 = 3^9.  The theorem
-- below proves equality of the integer numerators only.  Its boundary record
-- explicitly blocks semantic promotion of that digit coincidence.
------------------------------------------------------------------------

ninetyPercentThreeAxisNumeratorIs19683 :
  Branch.jointAccessibleNumerator 3 3 9 ≡ 19683
ninetyPercentThreeAxisNumeratorIs19683 =
  Branch.threeAxisNinetyPercentNumerator

ninetyPercentThreeAxisDenominatorIs1000 :
  Branch.jointAccessibleDenominator 3 10 ≡ 1000
ninetyPercentThreeAxisDenominatorIs1000 =
  Branch.threeAxisNinetyPercentDenominator

ninetyPercentThreeAxisNumeratorMatchesJFineFrequency :
  Branch.jointAccessibleNumerator 3 3 9 ≡ Scale.jFineFrequency
ninetyPercentThreeAxisNumeratorMatchesJFineFrequency =
  trans Branch.threeAxisNinetyPercentNumerator
        (sym J.jFineFrequencyIsThreePowerNine)

------------------------------------------------------------------------
-- Per-axis 10% gain over three simultaneous axes.
------------------------------------------------------------------------

threeAxisTenPercentGainNumeratorIs1331 : Branch.pow 11 3 ≡ 1331
threeAxisTenPercentGainNumeratorIs1331 =
  Branch.threeAxisTenPercentGainNumerator

threeAxisTenPercentGainDenominatorIs1000 : Branch.pow 10 3 ≡ 1000
threeAxisTenPercentGainDenominatorIs1000 =
  Branch.threeAxisTenPercentGainDenominator

------------------------------------------------------------------------
-- Decimal coarse/fine specimen.
------------------------------------------------------------------------

nineRefinementDepthOne : Decimal.decimalRefinementNumerator Decimal.d9 1 ≡ 99
nineRefinementDepthOne = Decimal.nineDepthOne

nineRefinementDepthTwo : Decimal.decimalRefinementNumerator Decimal.d9 2 ≡ 999
nineRefinementDepthTwo = Decimal.nineDepthTwo

nineCompletedComplementGapIsZero :
  Decimal.completedGapNumeratorOverNine Decimal.d9 ≡ 0
nineCompletedComplementGapIsZero = Decimal.nineCompletedGapIsZero

allDecimalDigitsSplitNextIntegerIntoCompletedPlusComplement :
  (digit : Decimal.DecimalDigit) →
  Decimal.nextIntegerNumeratorOverNine digit
  ≡ Decimal.completedRefinementNumeratorOverNine digit
      + Decimal.completedGapNumeratorOverNine digit
allDecimalDigitsSplitNextIntegerIntoCompletedPlusComplement =
  Decimal.nextIntegerSplitsAsCompletedPlusGap

------------------------------------------------------------------------
-- Existing JCoarse/JFine fibre boundary remains authoritative.
------------------------------------------------------------------------

fixedJFineValueDoesNotAcquireThreePowerNineFibreCardinality :
  J.JCoarseFineEvaluationBoundary.fixedValueAssignmentFibreHasCardinalityThreePowerNine
    J.canonicalJCoarseFineEvaluationBoundary
  ≡ false
fixedJFineValueDoesNotAcquireThreePowerNineFibreCardinality = refl

record JCoarseFineBranchingCriticalityBoundary : Set where
  constructor j-coarse-fine-branching-criticality-boundary
  field
    jFineIsProbability : Bool
    jFineIsProbabilityIsFalse : jFineIsProbability ≡ false
    ninetyPercentDigitCoincidenceIsSemanticIdentity : Bool
    ninetyPercentDigitCoincidenceIsSemanticIdentityIsFalse :
      ninetyPercentDigitCoincidenceIsSemanticIdentity ≡ false
    historicalFiveEighteenthsWasDerivedFromBranchingTheory : Bool
    historicalFiveEighteenthsWasDerivedFromBranchingTheoryIsFalse :
      historicalFiveEighteenthsWasDerivedFromBranchingTheory ≡ false
    independentAxisModelAssertedEmpirically : Bool
    independentAxisModelAssertedEmpiricallyIsFalse :
      independentAxisModelAssertedEmpirically ≡ false
    infiniteDecimalRealLimitProvedHere : Bool
    infiniteDecimalRealLimitProvedHereIsFalse :
      infiniteDecimalRealLimitProvedHere ≡ false
    multitypeSpectralRadiusCriterionProvedHere : Bool
    multitypeSpectralRadiusCriterionProvedHereIsFalse :
      multitypeSpectralRadiusCriterionProvedHere ≡ false

canonicalJCoarseFineBranchingCriticalityBoundary :
  JCoarseFineBranchingCriticalityBoundary
canonicalJCoarseFineBranchingCriticalityBoundary =
  j-coarse-fine-branching-criticality-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
