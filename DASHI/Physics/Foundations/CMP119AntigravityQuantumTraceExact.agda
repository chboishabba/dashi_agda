{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityQuantumTraceExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _<_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.Foundations.CMP119GibbsDiagonalTraceCancellationExact as Cancel
import DASHI.Physics.Foundations.CMP119GibbsDiagonalTraceSignExact as Sign
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- RENORMALIZED / QUANTUM TRACE ATTACHMENT
--
-- The classical d=4 Gibbs action-trace contribution is already cancelled by
-- CMP119GibbsDiagonalTraceCancellationExact.  What remains in the active
-- connected numerator is the weighted trace of the selected insertion
-- variation.
--
-- This module deliberately does not call a beta-function coefficient, anomaly
-- coefficient, or continuum formula "the CMP119 trace".  Instead it exposes
-- the exact same-object attachment required to make such a source theorem pay:
--
--   selected finite trace insertion variation
--     = declared renormalized/quantum trace variation
--
-- on the SAME literal finite measure.
--
-- Once that equality is supplied, strict negativity of the single weighted
-- quantum trace numerator plus Z>0 closes the entire four-diagonal sign.
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

  selectedTraceVariation : Configuration → ℚ
  selectedTraceVariation =
    Cancel.traceInsertionVariation
      dataSet directions laws actionTraceZero

  selectedTraceNumerator : ℚ
  selectedTraceNumerator =
    Cancel.traceInsertionNumerator
      dataSet directions laws actionTraceZero

  activeConnectedNumerator : ℚ
  activeConnectedNumerator =
    Cancel.activeConnectedNumerator
      dataSet directions laws actionTraceZero

  record RenormalizedTraceAttachment : Set₁ where
    field
      quantumTraceVariation : Configuration → ℚ

      selectedTraceIsQuantumTrace :
        ∀ configuration →
        selectedTraceVariation configuration
        ≡ quantumTraceVariation configuration

  open RenormalizedTraceAttachment public

  quantumTraceNumerator :
    RenormalizedTraceAttachment → ℚ
  quantumTraceNumerator attachment =
    Physical.haarIntegral measure
      (λ configuration →
        Physical.density measure configuration
        * quantumTraceVariation attachment configuration)

  selectedTraceNumeratorIsQuantumTraceNumerator :
    (attachment : RenormalizedTraceAttachment) →
    selectedTraceNumerator ≡ quantumTraceNumerator attachment
  selectedTraceNumeratorIsQuantumTraceNumerator attachment =
    Integral.haarIntegralCongruent laws _ _
      (λ configuration →
        cong
          (λ traceValue →
            Physical.density measure configuration * traceValue)
          (selectedTraceIsQuantumTrace attachment configuration))

  record QuantumTraceSignInput
      (attachment : RenormalizedTraceAttachment) : Set where
    field
      partitionPositive :
        0ℚ < Physical.partitionFunction measure

      quantumTraceNegative :
        quantumTraceNumerator attachment < 0ℚ

  open QuantumTraceSignInput public

  selectedTraceNumeratorNegative :
    (attachment : RenormalizedTraceAttachment) →
    QuantumTraceSignInput attachment →
    selectedTraceNumerator < 0ℚ
  selectedTraceNumeratorNegative attachment input =
    subst
      (λ value → value < 0ℚ)
      (sym (selectedTraceNumeratorIsQuantumTraceNumerator attachment))
      (quantumTraceNegative input)

  quantumTraceSignClosesActiveConnectedNumerator :
    (attachment : RenormalizedTraceAttachment) →
    QuantumTraceSignInput attachment →
    activeConnectedNumerator < 0ℚ
  quantumTraceSignClosesActiveConnectedNumerator attachment input =
    Sign.activeConnectedNumeratorNegative
      dataSet directions laws actionTraceZero
      (record
        { Sign.PositivePartitionNegativeTraceInput.partitionPositive =
            partitionPositive input
        ; Sign.PositivePartitionNegativeTraceInput.traceInsertionNegative =
            selectedTraceNumeratorNegative attachment input
        })
