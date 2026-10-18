{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityBetaTraceQuantumClosureExact where

open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _<_)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Foundations.CMP119AntigravityQuantumTraceExact as Quantum
import DASHI.Physics.Foundations.CMP119AntigravityBetaTraceBridgeExact as BetaTrace
import DASHI.Physics.Foundations.CMP119GibbsDiagonalTraceCancellationExact as Cancel
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- BETA/F^2 ATTACHMENT -> QUANTUM TRACE SIGN -> NEGATIVE ACTIVE SOURCE
--
-- This composes the two preceding compiler layers without adding physics.
-- A beta/F^2 attachment is useful only after it has been welded to the exact
-- weighted quantum trace numerator selected on the same finite measure.
------------------------------------------------------------------------

module _
    {Configuration MetricPerturbation : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (dataSet :
      Gibbs.GibbsMetricInsertionData
        Configuration MetricPerturbation measure)
    (directions : Cancel.FourDiagonalPerturbations MetricPerturbation)
    (laws : Integral.RationalFiniteMeasureIntegrationLaws measure)
    (actionTraceZero :
      ∀ configuration →
      Gibbs.actionVariation dataSet (Cancel.h00 directions) configuration
      + Gibbs.actionVariation dataSet (Cancel.h11 directions) configuration
      + Gibbs.actionVariation dataSet (Cancel.h22 directions) configuration
      + Gibbs.actionVariation dataSet (Cancel.h33 directions) configuration
      ≡ 0ℚ)
  where

  record BetaTraceQuantumClosureInput : Set₁ where
    field
      traceAttachment :
        Quantum.RenormalizedTraceAttachment
          dataSet directions laws actionTraceZero

      partitionPositive :
        0ℚ < Physical.partitionFunction measure

      betaTraceAttachment :
        BetaTrace.BetaTraceNumeratorAttachment
          (Quantum.quantumTraceNumerator
            dataSet directions laws actionTraceZero
            traceAttachment)

  open BetaTraceQuantumClosureInput public

  betaTraceGivesQuantumTraceNegative :
    (input : BetaTraceQuantumClosureInput) →
    Quantum.quantumTraceNumerator
      dataSet directions laws actionTraceZero
      (traceAttachment input)
    < 0ℚ
  betaTraceGivesQuantumTraceNegative input =
    BetaTrace.betaTraceAttachmentGivesQuantumTraceNegative
      (betaTraceAttachment input)

  betaTraceClosesNegativeActiveConnectedNumerator :
    BetaTraceQuantumClosureInput →
    Quantum.activeConnectedNumerator
      dataSet directions laws actionTraceZero
    < 0ℚ
  betaTraceClosesNegativeActiveConnectedNumerator input =
    Quantum.quantumTraceSignClosesActiveConnectedNumerator
      dataSet directions laws actionTraceZero
      (traceAttachment input)
      (record
        { Quantum.QuantumTraceSignInput.partitionPositive =
            partitionPositive input
        ; Quantum.QuantumTraceSignInput.quantumTraceNegative =
            betaTraceGivesQuantumTraceNegative input
        })
