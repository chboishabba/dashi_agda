{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralFourReceiptBetaRound471Exact where

------------------------------------------------------------------------
-- ROUND471: FOUR JOINT RECEIPT SUMS -> ALL-GROUP POSITIVE BETA
-- WITHOUT INTRODUCING UNOBSERVED "TRUE ORBIT VALUES".
--
-- The configured interval/integral layer naturally proves
--
--   L_1+...+L_4 <= r_n <= U_1+...+U_4
--
-- for the SAME literal regular remainder r_n.  The historical
-- FourOrbitStepEnclosure additionally introduced four exact orbit values S_i.
-- Those values are useful for audit, but they are not observed by the beta
-- consumer.  This module uses the least-privilege receipt ABI directly.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _≤_; -_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanCompactSimpleOneLoopRemainderBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCompactSimpleUniversalBetaFloorExact as Universal
import DASHI.Physics.YangMills.CompactSimpleClassificationAdjointCasimirExact as Classified
import DASHI.Physics.YangMills.CompactSimpleClassification as Class
import DASHI.Physics.YangMills.BalabanTopDownOneLoopRemainderBudgetExact as SU2Budget

record FourJointReceiptBounds : Set₁ where
  field
    lower1 lower2 lower3 lower4 : ℚ
    upper1 upper2 upper3 upper4 : ℚ
    regularRemainder : ℚ

    receiptLowerBoundsRemainder :
      lower1 + lower2 + lower3 + lower4
      ≤ regularRemainder

    remainderBelowReceiptUpper :
      regularRemainder
      ≤ upper1 + upper2 + upper3 + upper4

    totalLowerInsideHalf :
      - SU2Budget.half
      ≤ lower1 + lower2 + lower3 + lower4

    totalUpperInsideHalf :
      upper1 + upper2 + upper3 + upper4
      ≤ SU2Budget.half

open FourJointReceiptBounds public

receiptRemainderLowerHalf :
  (bounds : FourJointReceiptBounds) →
  - SU2Budget.half ≤ regularRemainder bounds
receiptRemainderLowerHalf bounds =
  ℚP.≤-trans
    (totalLowerInsideHalf bounds)
    (receiptLowerBoundsRemainder bounds)

receiptRemainderUpperHalf :
  (bounds : FourJointReceiptBounds) →
  regularRemainder bounds ≤ SU2Budget.half
receiptRemainderUpperHalf bounds =
  ℚP.≤-trans
    (remainderBelowReceiptUpper bounds)
    (totalUpperInsideHalf bounds)

record ClassifiedGroupFourReceiptBetaTrajectory
    (lieType : Class.SimpleLieType)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    stepReceipts : Nat → FourJointReceiptBounds

    betaIsGroupUniversalPlusReceiptRemainder :
      ∀ step →
      Flow.beta trajectory (suc step)
      ≡
      Budget.groupUniversalCoefficient
        Classified.classificationStrictCasimirCarrier lieType
      + regularRemainder (stepReceipts step)

open ClassifiedGroupFourReceiptBetaTrajectory public

fourReceiptHalfRemainderEnclosure :
  ∀ {lieType trajectory} →
  ClassifiedGroupFourReceiptBetaTrajectory lieType trajectory →
  Budget.CompactSimpleRegularRemainderEnclosure
    Classified.classificationStrictCasimirCarrier lieType
    trajectory
fourReceiptHalfRemainderEnclosure {lieType = lieType} dataSet = record
  { Budget.CompactSimpleRegularRemainderEnclosure.radius =
      SU2Budget.half
  ; Budget.CompactSimpleRegularRemainderEnclosure.radiusNonnegative =
      SU2Budget.halfNonnegative
  ; Budget.CompactSimpleRegularRemainderEnclosure.radiusBelowUniversal =
      Universal.uniformRemainderBelowEveryCompactSimpleCoefficient
        SU2Budget.half lieType SU2Budget.halfBelowElevenTwelfths
  ; Budget.CompactSimpleRegularRemainderEnclosure.regularRemainder =
      λ step → regularRemainder (stepReceipts dataSet step)
  ; Budget.CompactSimpleRegularRemainderEnclosure.betaIsUniversalPlusRegular =
      betaIsGroupUniversalPlusReceiptRemainder dataSet
  ; Budget.CompactSimpleRegularRemainderEnclosure.regularLower =
      λ step → receiptRemainderLowerHalf (stepReceipts dataSet step)
  ; Budget.CompactSimpleRegularRemainderEnclosure.regularUpper =
      λ step → receiptRemainderUpperHalf (stepReceipts dataSet step)
  }

fourLiteralReceiptBoundsGiveUniformPositiveBeta :
  ∀ {lieType trajectory} →
  ClassifiedGroupFourReceiptBetaTrajectory lieType trajectory →
  Flow.UniformBetaEnclosure trajectory
fourLiteralReceiptBoundsGiveUniformPositiveBeta dataSet =
  Budget.compactSimpleRemainderGivesUniformPositiveBeta
    (fourReceiptHalfRemainderEnclosure dataSet)

round471ReceiptToPositiveBetaCompilerLevel : ProofLevel
round471ReceiptToPositiveBetaCompilerLevel = machineChecked

-- The surviving one-loop physical leaf is now exactly:
--   * construct the literal Wilson/FP/Haar evaluator in source normalization;
--   * certify four joint lower/upper receipt totals;
--   * prove their combined lower/upper sums lie in [-1/2,1/2];
--   * identify beta = C_A*11/24 + that SAME receipt-bounded remainder.
--
-- No exact per-orbit latent value is required by the consumer.
literalRound471FourJointReceiptEvaluationLevel : ProofLevel
literalRound471FourJointReceiptEvaluationLevel = conditional
