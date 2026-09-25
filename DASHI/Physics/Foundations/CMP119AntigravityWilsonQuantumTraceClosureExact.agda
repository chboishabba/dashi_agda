{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityWilsonQuantumTraceClosureExact where

open import Data.Rational.Base using (ℚ; 0ℚ; _<_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119AntigravityQuantumTraceExact as Quantum
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTraceInsertionReductionExact as WilsonTrace
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- WILSON/GIBBS -> QUANTUM TRACE -> NEGATIVE ACTIVE SOURCE
--
-- This is the theorem-producing AG-2/AG-4 compiler.  It specializes the
-- generic quantum-trace attachment to the exact four canonical Wilson metric
-- directions.  No component-by-component target values are required.
--
-- The only non-algebraic inputs left here are:
--   (1) the selected trace variation is the declared renormalized trace;
--   (2) the literal partition function is positive;
--   (3) the weighted renormalized trace numerator is strictly negative.
--
-- A later same-object weld must still identify this selected Wilson/Gibbs
-- insertion with the actual CMP119 source insertion.  This module does not
-- manufacture that physical identification.
------------------------------------------------------------------------

module _
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (selectedInsertion : Wilson.ClassicalWilsonSelectedInsertion Configuration)
    (laws : Integral.RationalFiniteMeasureIntegrationLaws measure)
  where

  dataSet = WilsonTrace.gibbsData selectedInsertion laws

  directions = WilsonTrace.diagonalDirections

  actionTraceZero =
    WilsonTrace.actionTraceZero selectedInsertion laws

  RenormalizedTraceAttachment : Set₁
  RenormalizedTraceAttachment =
    Quantum.RenormalizedTraceAttachment
      dataSet directions laws actionTraceZero

  quantumTraceNumerator :
    RenormalizedTraceAttachment → ℚ
  quantumTraceNumerator =
    Quantum.quantumTraceNumerator
      dataSet directions laws actionTraceZero

  record WilsonQuantumTraceClosureInput : Set₁ where
    field
      traceAttachment :
        RenormalizedTraceAttachment

      partitionPositive :
        0ℚ < Physical.partitionFunction measure

      quantumTraceNegative :
        quantumTraceNumerator traceAttachment < 0ℚ

  open WilsonQuantumTraceClosureInput public

  selectedWilsonActiveConnectedNumerator : ℚ
  selectedWilsonActiveConnectedNumerator =
    WilsonTrace.activeConnectedNumerator selectedInsertion laws

  compileWilsonQuantumTraceNegativeActive :
    WilsonQuantumTraceClosureInput →
    selectedWilsonActiveConnectedNumerator < 0ℚ
  compileWilsonQuantumTraceNegativeActive input =
    Quantum.quantumTraceSignClosesActiveConnectedNumerator
      dataSet directions laws actionTraceZero
      (traceAttachment input)
      (record
        { Quantum.QuantumTraceSignInput.partitionPositive =
            partitionPositive input
        ; Quantum.QuantumTraceSignInput.quantumTraceNegative =
            quantumTraceNegative input
        })

fourDiagonalToSingleTraceCompilerClosed : Bool
fourDiagonalToSingleTraceCompilerClosed = true

fourDiagonalToSingleTraceCompilerClosedIsTrue :
  fourDiagonalToSingleTraceCompilerClosed ≡ true
fourDiagonalToSingleTraceCompilerClosedIsTrue = refl

quantumTraceSameObjectAttachmentStillRequired : Bool
quantumTraceSameObjectAttachmentStillRequired = true

quantumTraceSameObjectAttachmentStillRequiredIsTrue :
  quantumTraceSameObjectAttachmentStillRequired ≡ true
quantumTraceSameObjectAttachmentStillRequiredIsTrue = refl

quantumTraceStrictSignStillRequired : Bool
quantumTraceStrictSignStillRequired = true

quantumTraceStrictSignStillRequiredIsTrue :
  quantumTraceStrictSignStillRequired ≡ true
quantumTraceStrictSignStillRequiredIsTrue = refl

selectedPartitionPositivityStillRequired : Bool
selectedPartitionPositivityStillRequired = true

selectedPartitionPositivityStillRequiredIsTrue :
  selectedPartitionPositivityStillRequired ≡ true
selectedPartitionPositivityStillRequiredIsTrue = refl
