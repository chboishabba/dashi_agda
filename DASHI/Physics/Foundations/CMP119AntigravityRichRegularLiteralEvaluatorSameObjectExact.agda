{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRichRegularLiteralEvaluatorSameObjectExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (_+_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityLiteralEvaluatorRegularReceiptSameObjectExact as EvalReceipt
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Literal
import DASHI.Physics.YangMills.BalabanLiteralOneLoopFourOrbitSameObjectExact as FourOrbit
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact as OrbitSum
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CONFIGURED RICH REGULAR REMAINDER USES THE LITERAL EVALUATOR'S RECEIPTS
--
-- The only source-facing identification here is `partitionSameLiteralEvaluator`.
-- Once that is supplied, both configured rich remainder bounds are transported
-- to the exact lower/upper sums owned by the literal Wilson/FP/Haar evaluator,
-- and therefore to its four joint orbit folds.
------------------------------------------------------------------------

record RichRegularLiteralEvaluatorSameObject
    {expressions ward scalarData}
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ)
    (step : Nat)
    (evaluator : Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData) : Set₁ where
  field
    partitionSameLiteralEvaluator :
      Rich.partition rich step ≡ EvalReceipt.literalEvaluatorPartition evaluator

open RichRegularLiteralEvaluatorSameObject public

richLowerReceiptSumSameLiteralEvaluator :
  ∀ {expressions ward scalarData rich step evaluator} →
  RichRegularLiteralEvaluatorSameObject
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    rich step evaluator →
  Integral.boxLowerSum
    (Rich.regularBoxReceipts (Rich.partition rich step))
  ≡ FourOrbit.literalRegularLowerSum evaluator
richLowerReceiptSumSameLiteralEvaluator sameObject =
  trans
    (cong
      (λ partition → Integral.boxLowerSum (Rich.regularBoxReceipts partition))
      (partitionSameLiteralEvaluator sameObject))
    (EvalReceipt.literalEvaluatorRegularLowerReceiptSumExact _)

richUpperReceiptSumSameLiteralEvaluator :
  ∀ {expressions ward scalarData rich step evaluator} →
  RichRegularLiteralEvaluatorSameObject
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    rich step evaluator →
  Integral.boxUpperSum
    (Rich.regularBoxReceipts (Rich.partition rich step))
  ≡ FourOrbit.literalRegularUpperSum evaluator
richUpperReceiptSumSameLiteralEvaluator sameObject =
  trans
    (cong
      (λ partition → Integral.boxUpperSum (Rich.regularBoxReceipts partition))
      (partitionSameLiteralEvaluator sameObject))
    (EvalReceipt.literalEvaluatorRegularUpperReceiptSumExact _)

richLowerReceiptSumIsFourJointOrbits :
  ∀ {expressions ward scalarData rich step evaluator} →
  RichRegularLiteralEvaluatorSameObject
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    rich step evaluator →
  Integral.boxLowerSum
    (Rich.regularBoxReceipts (Rich.partition rich step))
  ≡
    OrbitSum.oneOuterOrbitSum
      (FourOrbit.literalLowerContribution evaluator)
    + OrbitSum.twoOuterOrbitSum
      (FourOrbit.literalLowerContribution evaluator)
    + OrbitSum.threeOuterOrbitSum
      (FourOrbit.literalLowerContribution evaluator)
    + OrbitSum.fourOuterOrbitSum
      (FourOrbit.literalLowerContribution evaluator)
richLowerReceiptSumIsFourJointOrbits sameObject =
  trans
    (richLowerReceiptSumSameLiteralEvaluator sameObject)
    (FourOrbit.literalLowerSumIsFourJointOrbits _)

richUpperReceiptSumIsFourJointOrbits :
  ∀ {expressions ward scalarData rich step evaluator} →
  RichRegularLiteralEvaluatorSameObject
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    rich step evaluator →
  Integral.boxUpperSum
    (Rich.regularBoxReceipts (Rich.partition rich step))
  ≡
    OrbitSum.oneOuterOrbitSum
      (FourOrbit.literalUpperContribution evaluator)
    + OrbitSum.twoOuterOrbitSum
      (FourOrbit.literalUpperContribution evaluator)
    + OrbitSum.threeOuterOrbitSum
      (FourOrbit.literalUpperContribution evaluator)
    + OrbitSum.fourOuterOrbitSum
      (FourOrbit.literalUpperContribution evaluator)
richUpperReceiptSumIsFourJointOrbits sameObject =
  trans
    (richUpperReceiptSumSameLiteralEvaluator sameObject)
    (FourOrbit.literalUpperSumIsFourJointOrbits _)

richRegularLiteralEvaluatorSameObjectCompilerLevel : ProofLevel
richRegularLiteralEvaluatorSameObjectCompilerLevel = machineChecked

richPartitionLiteralEvaluatorIdentificationLevel : ProofLevel
richPartitionLiteralEvaluatorIdentificationLevel = conditional
