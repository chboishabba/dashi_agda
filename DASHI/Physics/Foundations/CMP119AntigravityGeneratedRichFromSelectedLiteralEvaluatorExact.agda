{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityGeneratedRichFromSelectedLiteralEvaluatorExact where

------------------------------------------------------------------------
-- FINITE-MODE/GAUSSIAN MAX-CUT: REMOVE INDEPENDENT PARTITION PAYMENT
--
-- The literal Wilson/Faddeev-Popov/Haar evaluator is selected FIRST.
-- Rich.partition(k) is then definitionally its finite generated grid, with
-- lower/upper receipt bounds referring to those very generated receipts.
-- No arbitrary configured partition is available to change the source.
--
-- Literal Ward/shell normalization, integration and finite epsilon matching
-- remain actual analytic obligations. This record does not discharge them
-- merely by choosing a representation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.Foundations.CMP119AntigravityLiteralEvaluatorRegularReceiptSameObjectExact as EvalReceipt
import DASHI.Physics.Foundations.CMP119AntigravityRichRegularLiteralEvaluatorSameObjectExact as Same
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Literal

record SelectedEvaluatorGeneratedRichSource
    {expressions ward scalarData}
    (evaluatorAt : Nat →
      Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData) : Set₁ where
  field
    casimirAdjoint inversePiSquared logBlocking : Nat → Bishop.ℝ
    scalarIntegral regularRemainder coefficient : Nat → Bishop.ℝ

    colorTensorReductionExact : Nat → Set
    wardTransverseProjectorExact : Nat → Set
    massAndLongitudinalTermsVanish : Nat → Set
    infraredSingularIntegrandExact : Nat → Set

    selectedShellNormalization : ∀ k →
      scalarIntegral k ≡ Bishop._*_
        (Bishop._*_
          (UV.embed Integral.elevenTwentyFourth)
          (casimirAdjoint k))
        (Bishop._*_ (inversePiSquared k) (logBlocking k))

    selectedRegularLower : ∀ k →
      Bishop._≤_
        (UV.embed
          (Integral.boxLowerSum
            (Rich.regularBoxReceipts
              (EvalReceipt.literalEvaluatorPartition (evaluatorAt k)))))
        (regularRemainder k)

    selectedRegularUpper : ∀ k →
      Bishop._≤_
        (regularRemainder k)
        (UV.embed
          (Integral.boxUpperSum
            (Rich.regularBoxReceipts
              (EvalReceipt.literalEvaluatorPartition (evaluatorAt k)))))

    selectedCoefficient : ∀ k →
      coefficient k ≡
        Bishop._+_ (scalarIntegral k) (regularRemainder k)

open SelectedEvaluatorGeneratedRichSource public

asGeneratedRich :
  ∀ {expressions ward scalarData evaluatorAt} →
  SelectedEvaluatorGeneratedRichSource
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    evaluatorAt →
  Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ
asGeneratedRich {evaluatorAt = evaluatorAt} source = record
  { Rich.LiteralBrillouinIntegralPhysicalData.rational = UV.embed
  ; Rich.LiteralBrillouinIntegralPhysicalData.add = Bishop._+_
  ; Rich.LiteralBrillouinIntegralPhysicalData.multiply = Bishop._*_
  ; Rich.LiteralBrillouinIntegralPhysicalData.subtract = Bishop._-_
  ; Rich.LiteralBrillouinIntegralPhysicalData.LessEqual = Bishop._≤_
  ; Rich.LiteralBrillouinIntegralPhysicalData.partition =
      λ k → EvalReceipt.literalEvaluatorPartition (evaluatorAt k)
  ; Rich.LiteralBrillouinIntegralPhysicalData.casimirAdjoint =
      casimirAdjoint source
  ; Rich.LiteralBrillouinIntegralPhysicalData.inversePiSquared =
      inversePiSquared source
  ; Rich.LiteralBrillouinIntegralPhysicalData.logBlocking =
      logBlocking source
  ; Rich.LiteralBrillouinIntegralPhysicalData.scalarIntegral =
      scalarIntegral source
  ; Rich.LiteralBrillouinIntegralPhysicalData.regularRemainder =
      regularRemainder source
  ; Rich.LiteralBrillouinIntegralPhysicalData.coefficient =
      coefficient source
  ; Rich.LiteralBrillouinIntegralPhysicalData.colorTensorReductionExact =
      colorTensorReductionExact source
  ; Rich.LiteralBrillouinIntegralPhysicalData.wardTransverseProjectorExact =
      wardTransverseProjectorExact source
  ; Rich.LiteralBrillouinIntegralPhysicalData.massAndLongitudinalTermsVanish =
      massAndLongitudinalTermsVanish source
  ; Rich.LiteralBrillouinIntegralPhysicalData.infraredSingularIntegrandExact =
      infraredSingularIntegrandExact source
  ; Rich.LiteralBrillouinIntegralPhysicalData.infraredShellIntegralLogLExact =
      selectedShellNormalization source
  ; Rich.LiteralBrillouinIntegralPhysicalData.regularRemainderBetweenReceiptSums =
      selectedRegularLower source
  ; Rich.LiteralBrillouinIntegralPhysicalData.regularRemainderBelowReceiptSum =
      selectedRegularUpper source
  ; Rich.LiteralBrillouinIntegralPhysicalData.coefficientDefinition =
      selectedCoefficient source
  }

generatedPartitionEqualsSelectedEvaluator :
  ∀ {expressions ward scalarData evaluatorAt}
    (source : SelectedEvaluatorGeneratedRichSource
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      evaluatorAt) →
  ∀ k →
  Rich.partition (asGeneratedRich source) k
  ≡ EvalReceipt.literalEvaluatorPartition (evaluatorAt k)
generatedPartitionEqualsSelectedEvaluator source k = refl

asSelectedPartitionSameObject :
  ∀ {expressions ward scalarData evaluatorAt}
    (source : SelectedEvaluatorGeneratedRichSource
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      evaluatorAt) →
  ∀ k →
  Same.RichRegularLiteralEvaluatorSameObject
    (asGeneratedRich source) k (evaluatorAt k)
asSelectedPartitionSameObject source k = record
  { Same.RichRegularLiteralEvaluatorSameObject.partitionSameLiteralEvaluator =
      generatedPartitionEqualsSelectedEvaluator source k
  }
