module DASHI.Physics.Closure.FactorVecAverageVsSumReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.RGContractionExplicitReceipt as Explicit
import DASHI.Physics.Closure.RGOperatorNormReceipt as Norm

data FactorVecRGChildAggregation : Set where
  parentFibreSumRecorded : FactorVecRGChildAggregation
  normalizedChildAverageRequired : FactorVecRGChildAggregation

data FactorVecRGNormConclusion : Set where
  sumGivesBranchingTimesAlphaOne : FactorVecRGNormConclusion
  averageGivesAlphaOne : FactorVecRGNormConclusion

data FactorVecRGNormalizationBlocker : Set where
  existingReceiptUsesParentSumLanguage : FactorVecRGNormalizationBlocker
  normalizedAverageMapNeedsDownstreamConsumption : FactorVecRGNormalizationBlocker
  clayRGContinuumLimitStillOpen : FactorVecRGNormalizationBlocker

canonicalFactorVecRGNormalizationBlockers :
  List FactorVecRGNormalizationBlocker
canonicalFactorVecRGNormalizationBlockers =
  existingReceiptUsesParentSumLanguage
  ∷ normalizedAverageMapNeedsDownstreamConsumption
  ∷ clayRGContinuumLimitStillOpen
  ∷ []

factorVecAverageStatement : String
factorVecAverageStatement =
  "The existing explicit RG receipt records a parent-fibre sum target.  The alpha1 operator norm is exact only for the normalized child-average map; the unnormalized sum has branching-factor norm b*alpha1."

record FactorVecAverageVsSumReceipt : Setω where
  field
    explicitRGReceipt :
      Explicit.RGContractionExplicitReceipt

    explicitRGStillUsesSumLanguage :
      Explicit.operatorFormula explicitRGReceipt
      ≡
      Explicit.weightedFactorVecParentSum

    operatorNormReceipt :
      Norm.RGOperatorNormReceipt

    priorNormEqualityStillOpen :
      Norm.operatorNormEqualityProved operatorNormReceipt ≡ false

    branchingFactor :
      Nat

    branchingFactorIsThree :
      branchingFactor ≡ 3

    existingAggregation :
      FactorVecRGChildAggregation

    existingAggregationIsParentSum :
      existingAggregation ≡ parentFibreSumRecorded

    requiredAggregation :
      FactorVecRGChildAggregation

    requiredAggregationIsAverage :
      requiredAggregation ≡ normalizedChildAverageRequired

    unnormalizedSumConclusion :
      FactorVecRGNormConclusion

    unnormalizedSumConclusionIsCanonical :
      unnormalizedSumConclusion ≡ sumGivesBranchingTimesAlphaOne

    normalizedAverageConclusion :
      FactorVecRGNormConclusion

    normalizedAverageConclusionIsCanonical :
      normalizedAverageConclusion ≡ averageGivesAlphaOne

    factorVecAverageVsSumRecorded :
      Bool

    factorVecAverageVsSumRecordedIsTrue :
      factorVecAverageVsSumRecorded ≡ true

    normalizedRGReceiptRequired :
      Bool

    normalizedRGReceiptRequiredIsTrue :
      normalizedRGReceiptRequired ≡ true

    operatorNormAlphaOneProvedForExistingSum :
      Bool

    operatorNormAlphaOneProvedForExistingSumIsFalse :
      operatorNormAlphaOneProvedForExistingSum ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    blockers :
      List FactorVecRGNormalizationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalFactorVecRGNormalizationBlockers

    statement :
      String

    statementIsCanonical :
      statement ≡ factorVecAverageStatement

    receiptBoundary :
      List String

open FactorVecAverageVsSumReceipt public

canonicalFactorVecAverageVsSumReceipt :
  FactorVecAverageVsSumReceipt
canonicalFactorVecAverageVsSumReceipt =
  record
    { explicitRGReceipt =
        Explicit.canonicalRGContractionExplicitReceipt
    ; explicitRGStillUsesSumLanguage =
        refl
    ; operatorNormReceipt =
        Norm.canonicalRGOperatorNormReceipt
    ; priorNormEqualityStillOpen =
        refl
    ; branchingFactor =
        3
    ; branchingFactorIsThree =
        refl
    ; existingAggregation =
        parentFibreSumRecorded
    ; existingAggregationIsParentSum =
        refl
    ; requiredAggregation =
        normalizedChildAverageRequired
    ; requiredAggregationIsAverage =
        refl
    ; unnormalizedSumConclusion =
        sumGivesBranchingTimesAlphaOne
    ; unnormalizedSumConclusionIsCanonical =
        refl
    ; normalizedAverageConclusion =
        averageGivesAlphaOne
    ; normalizedAverageConclusionIsCanonical =
        refl
    ; factorVecAverageVsSumRecorded =
        true
    ; factorVecAverageVsSumRecordedIsTrue =
        refl
    ; normalizedRGReceiptRequired =
        true
    ; normalizedRGReceiptRequiredIsTrue =
        refl
    ; operatorNormAlphaOneProvedForExistingSum =
        false
    ; operatorNormAlphaOneProvedForExistingSumIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; blockers =
        canonicalFactorVecRGNormalizationBlockers
    ; blockersAreCanonical =
        refl
    ; statement =
        factorVecAverageStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The current explicit RG surface is audited as sum-language, not an inhabited normalized-average proof"
        ∷ "The exact alpha1 norm is retained only as the normalized child-average RG target"
        ∷ "The Yang-Mills RG continuum and Clay promotion flags remain false"
        ∷ []
    }

factorVecAverageVsSumDoesNotPromoteClay :
  clayYangMillsPromoted canonicalFactorVecAverageVsSumReceipt ≡ false
factorVecAverageVsSumDoesNotPromoteClay =
  refl

