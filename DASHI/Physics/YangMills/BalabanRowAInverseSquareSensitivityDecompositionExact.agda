module DASHI.Physics.YangMills.BalabanRowAInverseSquareSensitivityDecompositionExact where

------------------------------------------------------------------------
-- ROW A: EXACT ADDITIVE DECOMPOSITION OF THE SHOOTING SENSITIVITY BUDGET
--
-- Primary source context:
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- This module does NOT assert the missing physical q<1 estimate.  It removes
-- one piece of bookkeeping from that estimate.  Once the literal cumulative
-- beta difference is split into
--
--   direct current-coupling response + propagated irrelevant/history response,
--
-- and each piece is bounded in the inverse-square shooting coordinate u=g^-2,
-- the total Lipschitz constant is exactly qDirect+qHistory.
--
-- Thus the remaining physical Row-A leaf can be attacked componentwise without
-- assigning exponential forgetting to the marginal running coupling itself.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record InverseSquareSensitivitySplit : Set₁ where
  field
    inputDistance : ℚ
    directDifference historyDifference totalDifference : ℚ
    qDirect qHistory : ℚ

    inputDistanceNonnegative : 0ℚ ≤ inputDistance
    directDifferenceNonnegative : 0ℚ ≤ directDifference
    historyDifferenceNonnegative : 0ℚ ≤ historyDifference
    qDirectNonnegative : 0ℚ ≤ qDirect
    qHistoryNonnegative : 0ℚ ≤ qHistory

    totalBelowSplit :
      totalDifference ≤ directDifference + historyDifference

    directSensitivity :
      directDifference ≤ qDirect * inputDistance

    historySensitivity :
      historyDifference ≤ qHistory * inputDistance

open InverseSquareSensitivitySplit public

combinedSensitivityConstant : InverseSquareSensitivitySplit → ℚ
combinedSensitivityConstant dataSet = qDirect dataSet + qHistory dataSet

splitSensitivityAddsExactly :
  (dataSet : InverseSquareSensitivitySplit) →
  totalDifference dataSet
  ≤ combinedSensitivityConstant dataSet * inputDistance dataSet
splitSensitivityAddsExactly dataSet =
  let
    direct = directDifference dataSet
    history = historyDifference dataSet
    qD = qDirect dataSet
    qH = qHistory dataSet
    d = inputDistance dataSet

    componentSum :
      direct + history ≤ qD * d + qH * d
    componentSum =
      ℚP.+-mono-≤
        (directSensitivity dataSet)
        (historySensitivity dataSet)

    afterSplit :
      totalDifference dataSet ≤ qD * d + qH * d
    afterSplit = ℚP.≤-trans (totalBelowSplit dataSet) componentSum
  in
  subst
    (λ upper → totalDifference dataSet ≤ upper)
    (ℚRing.solve-∀ qD qH d)
    afterSplit

record StrictInverseSquareSensitivitySplit : Set₁ where
  field
    split : InverseSquareSensitivitySplit
    combinedStrictlyBelowOne : combinedSensitivityConstant split < 1ℚ

open StrictInverseSquareSensitivitySplit public

strictSplitGivesSubunitTotalSensitivity :
  (dataSet : StrictInverseSquareSensitivitySplit) →
  totalDifference (split dataSet)
  ≤ combinedSensitivityConstant (split dataSet)
      * inputDistance (split dataSet)
strictSplitGivesSubunitTotalSensitivity dataSet =
  splitSensitivityAddsExactly (split dataSet)

rowAInverseSquareSensitivitySplitAlgebraLevel : ProofLevel
rowAInverseSquareSensitivitySplitAlgebraLevel = machineChecked

rowAInverseSquareSubunitAssemblyLevel : ProofLevel
rowAInverseSquareSubunitAssemblyLevel = machineChecked

-- Physical leaves still required on the literal same generated CMP109/CMP122
-- trajectory.  The direct part should be extracted from the differentiated
-- Gaussian/current five-channel beta law in u=g^-2; the history part should use
-- the already-separated contractive irrelevant response, while the marginal
-- coupling remains explicit in u.
literalDirectInverseSquareBetaSensitivityLevel : ProofLevel
literalDirectInverseSquareBetaSensitivityLevel = conditional

literalIrrelevantHistoryInverseSquareSensitivityLevel : ProofLevel
literalIrrelevantHistoryInverseSquareSensitivityLevel = conditional

literalCombinedInverseSquareSensitivityStrictlyBelowOneLevel : ProofLevel
literalCombinedInverseSquareSensitivityStrictlyBelowOneLevel = conditional
