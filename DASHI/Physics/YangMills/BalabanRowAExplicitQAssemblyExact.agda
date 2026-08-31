module DASHI.Physics.YangMills.BalabanRowAExplicitQAssemblyExact where

------------------------------------------------------------------------
-- ROW A: EXPLICIT q = qDirect + qHistory ASSEMBLY
--
-- The direct inverse-square response and the propagated irrelevant-history
-- response are now independently compiled to Lipschitz constants.  This module
-- places them on the SAME input distance and constructs the exact sensitivity
-- split consumed by the shooting contraction theorem.
--
-- No physical estimate is manufactured here.  The last scalar condition is
-- literally
--
--        qDirect + qHistory < 1.
--
-- Once the source-native direct/history packages and this strict inequality are
-- supplied on the same generated trajectory, all remaining q-assembly algebra
-- is theorem-exact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _+_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRowAInverseSquareSensitivityDecompositionExact as Split
import DASHI.Physics.YangMills.BalabanRowADirectQFromTubeExact as Direct
import DASHI.Physics.YangMills.BalabanIrrelevantRGMemoryContractionExact as Memory
import DASHI.Physics.YangMills.BalabanRowAIrrelevantHistorySensitivityCumulativeExact as History

record ExplicitRowAQAssemblyData : Set₁ where
  field
    directData : Direct.DirectTubeToInputSensitivity

    memory : Memory.ContractiveIrrelevantMemory
    projection : Memory.LipschitzIrrelevantBetaProjection memory
    historyResponse : History.IrrelevantHistoryInputResponse projection
    cutoff : Nat

    totalDifference : ℚ

    sameInputDistance :
      History.inputDistance historyResponse
      ≡ Direct.inputDistance directData

    totalBelowDirectPlusHistory :
      totalDifference
      ≤ Direct.cumulativeDirect directData
        + History.sumBetaDifference
            (Memory.betaDifference projection) cutoff

    combinedStrictlyBelowOne :
      Direct.directSensitivityConstant directData
        + History.historySensitivityConstant historyResponse
      < 1ℚ

open ExplicitRowAQAssemblyData public

historySensitivityOnDirectInput :
  (dataSet : ExplicitRowAQAssemblyData) →
  History.sumBetaDifference
      (Memory.betaDifference (projection dataSet))
      (cutoff dataSet)
  ≤ History.historySensitivityConstant (historyResponse dataSet)
      * Direct.inputDistance (directData dataSet)
historySensitivityOnDirectInput dataSet =
  subst
    (λ input →
      History.sumBetaDifference
          (Memory.betaDifference (projection dataSet))
          (cutoff dataSet)
      ≤ History.historySensitivityConstant (historyResponse dataSet) * input)
    (sameInputDistance dataSet)
    (History.cumulativeIrrelevantHistorySensitivity
      (historyResponse dataSet) (cutoff dataSet))

asInverseSquareSensitivitySplit :
  ExplicitRowAQAssemblyData → Split.InverseSquareSensitivitySplit
asInverseSquareSensitivitySplit dataSet = record
  { Split.InverseSquareSensitivitySplit.inputDistance =
      Direct.inputDistance (directData dataSet)
  ; Split.InverseSquareSensitivitySplit.directDifference =
      Direct.cumulativeDirect (directData dataSet)
  ; Split.InverseSquareSensitivitySplit.historyDifference =
      History.sumBetaDifference
        (Memory.betaDifference (projection dataSet)) (cutoff dataSet)
  ; Split.InverseSquareSensitivitySplit.totalDifference =
      totalDifference dataSet
  ; Split.InverseSquareSensitivitySplit.qDirect =
      Direct.directSensitivityConstant (directData dataSet)
  ; Split.InverseSquareSensitivitySplit.qHistory =
      History.historySensitivityConstant (historyResponse dataSet)
  ; Split.InverseSquareSensitivitySplit.inputDistanceNonnegative =
      Direct.inputDistanceNonnegative (directData dataSet)
  ; Split.InverseSquareSensitivitySplit.directDifferenceNonnegative =
      Direct.cumulativeDirectNonnegative (directData dataSet)
  ; Split.InverseSquareSensitivitySplit.historyDifferenceNonnegative =
      History.sumBetaDifferenceNonnegative
        (projection dataSet) (cutoff dataSet)
  ; Split.InverseSquareSensitivitySplit.qDirectNonnegative =
      Direct.directSensitivityConstantNonnegative (directData dataSet)
  ; Split.InverseSquareSensitivitySplit.qHistoryNonnegative =
      History.historySensitivityConstantNonnegative (historyResponse dataSet)
  ; Split.InverseSquareSensitivitySplit.totalBelowSplit =
      totalBelowDirectPlusHistory dataSet
  ; Split.InverseSquareSensitivitySplit.directSensitivity =
      Direct.directTubeBudgetGivesInputSensitivity (directData dataSet)
  ; Split.InverseSquareSensitivitySplit.historySensitivity =
      historySensitivityOnDirectInput dataSet
  }

asStrictInverseSquareSensitivitySplit :
  ExplicitRowAQAssemblyData → Split.StrictInverseSquareSensitivitySplit
asStrictInverseSquareSensitivitySplit dataSet = record
  { Split.StrictInverseSquareSensitivitySplit.split =
      asInverseSquareSensitivitySplit dataSet
  ; Split.StrictInverseSquareSensitivitySplit.combinedStrictlyBelowOne =
      combinedStrictlyBelowOne dataSet
  }

explicitRowAQGivesSubunitSensitivity :
  (dataSet : ExplicitRowAQAssemblyData) →
  totalDifference dataSet
  ≤ (Direct.directSensitivityConstant (directData dataSet)
      + History.historySensitivityConstant (historyResponse dataSet))
      * Direct.inputDistance (directData dataSet)
explicitRowAQGivesSubunitSensitivity dataSet =
  Split.strictSplitGivesSubunitTotalSensitivity
    (asStrictInverseSquareSensitivitySplit dataSet)

rowAExplicitQAssemblyAlgebraLevel : ProofLevel
rowAExplicitQAssemblyAlgebraLevel = machineChecked

rowAExplicitQSubunitSensitivityLevel : ProofLevel
rowAExplicitQSubunitSensitivityLevel = machineChecked

-- Remaining physical leaf: instantiate `directData`, `historyResponse`, and the
-- exact decomposition of the literal cumulative beta difference on the same
-- CMP109/CMP122 trajectory, then prove the displayed scalar q-sum is < 1.
literalRowAExplicitQAssemblyLevel : ProofLevel
literalRowAExplicitQAssemblyLevel = conditional
