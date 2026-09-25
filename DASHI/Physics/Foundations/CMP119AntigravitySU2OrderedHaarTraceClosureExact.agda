{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySU2OrderedHaarTraceClosureExact where

open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

import DASHI.Physics.Foundations.CMP119AntigravityQuantumTraceExact as Quantum
import DASHI.Physics.Foundations.CMP119AntigravityBetaTraceBridgeExact as BetaTrace
import DASHI.Physics.Foundations.CMP119AntigravityBetaTraceQuantumClosureExact as BetaClosure
import DASHI.Physics.Foundations.CMP119AntigravityOrderedHaarStrictPositivityExact as Ordered
import DASHI.Physics.Foundations.CMP119AntigravitySU2TraceConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravitySU2TraceNormalizationWeldExact as Normalization
import DASHI.Physics.Foundations.CMP119AntigravityCurvatureF2PositivityExact as CurvatureF2
import DASHI.Physics.Foundations.CMP119GibbsDiagonalTraceCancellationExact as Cancel
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- PREFERRED SU(2) TRACE CLOSURE ON THE ACTUAL HAAR FUNCTIONAL
--
-- This supersedes the exact-finite-quadrature sign route for a continuous
-- compact-group configuration carrier.
--
-- Inputs:
--   * ordered/linear laws for the actual Haar functional;
--   * positive-Haar minorants for the density and density*F^2;
--   * six-curvature F^2 family;
--   * explicit scalar 1/pi^2 normalization weld;
--   * selected renormalized trace same-object attachment.
--
-- Outputs:
--   Z > 0, N(F^2_normalized) > 0, Q_trace < 0, C_active < 0.
------------------------------------------------------------------------

module _
    {Configuration MetricPerturbation : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (dataSet :
      Gibbs.GibbsMetricInsertionData
        Configuration MetricPerturbation measure)
    (directions : Cancel.FourDiagonalPerturbations MetricPerturbation)
    (orderedLaws :
      Ordered.OrderedRationalHaarIntegrationLaws measure)
    (actionTraceZero :
      ∀ configuration →
      Gibbs.actionVariation dataSet (Cancel.h00 directions) configuration
      + Gibbs.actionVariation dataSet (Cancel.h11 directions) configuration
      + Gibbs.actionVariation dataSet (Cancel.h22 directions) configuration
      + Gibbs.actionVariation dataSet (Cancel.h33 directions) configuration
      ≡ 0ℚ)
  where

  laws = Ordered.linear orderedLaws

  record SU2OrderedHaarTraceClosureInput : Set₁ where
    field
      traceAttachment :
        Quantum.RenormalizedTraceAttachment
          dataSet directions laws actionTraceZero

      partitionWitness :
        Ordered.PositivePartitionHaarWitness orderedLaws

      curvatureF2Family :
        CurvatureF2.FiniteCurvatureF2Family Configuration

      weightedF2Witness :
        Ordered.PositiveWeightedF2HaarWitness
          orderedLaws
          (CurvatureF2.fieldStrengthSquare curvatureF2Family)

      TraceScalar : Set

      traceNormalization :
        Normalization.SU2TraceNormalizationWeld TraceScalar

      selectedTraceNumeratorMatchesNormalization :
        Normalization.selectedQuantumTraceNumerator traceNormalization
        ≡
        Quantum.quantumTraceNumerator
          dataSet directions laws actionTraceZero traceAttachment

      normalizedF2MatchesWeightedCurvatureNumerator :
        Normalization.normalizedF2Numerator traceNormalization
        ≡
        Ordered.fieldStrengthSquareNumerator
          {measure = measure}
          (CurvatureF2.fieldStrengthSquare curvatureF2Family)

  open SU2OrderedHaarTraceClosureInput public

  quantumTraceIsSU2NormalizedCurvatureF2 :
    (input : SU2OrderedHaarTraceClosureInput) →
    Quantum.quantumTraceNumerator
      dataSet directions laws actionTraceZero
      (traceAttachment input)
    ≡
    SU2.su2TraceRationalCoefficient
    *
    Ordered.fieldStrengthSquareNumerator
      {measure = measure}
      (CurvatureF2.fieldStrengthSquare (curvatureF2Family input))
  quantumTraceIsSU2NormalizedCurvatureF2 input =
    trans
      (sym (selectedTraceNumeratorMatchesNormalization input))
      (trans
        (Normalization.selectedTraceUsesNormalizedRationalF2
          (traceNormalization input))
        (cong
          (λ value → SU2.su2TraceRationalCoefficient * value)
          (normalizedF2MatchesWeightedCurvatureNumerator input)))

  betaTraceAttachment :
    (input : SU2OrderedHaarTraceClosureInput) →
    BetaTrace.BetaTraceNumeratorAttachment
      (Quantum.quantumTraceNumerator
        dataSet directions laws actionTraceZero
        (traceAttachment input))
  betaTraceAttachment input = record
    { BetaTrace.BetaTraceNumeratorAttachment.betaTraceCoefficient =
        SU2.su2TraceRationalCoefficient
    ; BetaTrace.BetaTraceNumeratorAttachment.fieldStrengthSquareNumerator =
        Ordered.fieldStrengthSquareNumerator
          {measure = measure}
          (CurvatureF2.fieldStrengthSquare (curvatureF2Family input))
    ; BetaTrace.BetaTraceNumeratorAttachment.selectedQuantumTraceIsBetaF2 =
        quantumTraceIsSU2NormalizedCurvatureF2 input
    ; BetaTrace.BetaTraceNumeratorAttachment.betaTraceCoefficientNegative =
        SU2.su2TraceCoefficientNegative
    ; BetaTrace.BetaTraceNumeratorAttachment.fieldStrengthSquareNumeratorPositive =
        Ordered.fieldStrengthSquareNumeratorPositive
          orderedLaws
          (CurvatureF2.fieldStrengthSquare (curvatureF2Family input))
          (weightedF2Witness input)
    }

  asBetaTraceQuantumClosureInput :
    SU2OrderedHaarTraceClosureInput →
    BetaClosure.BetaTraceQuantumClosureInput
      dataSet directions laws actionTraceZero
  asBetaTraceQuantumClosureInput input = record
    { BetaClosure.BetaTraceQuantumClosureInput.traceAttachment =
        traceAttachment input
    ; BetaClosure.BetaTraceQuantumClosureInput.partitionPositive =
        Ordered.partitionFunctionPositive
          orderedLaws (partitionWitness input)
    ; BetaClosure.BetaTraceQuantumClosureInput.betaTraceAttachment =
        betaTraceAttachment input
    }

  su2OrderedHaarTraceClosesNegativeActiveConnectedNumerator :
    SU2OrderedHaarTraceClosureInput →
    Quantum.activeConnectedNumerator
      dataSet directions laws actionTraceZero
    < 0ℚ
  su2OrderedHaarTraceClosesNegativeActiveConnectedNumerator input =
    BetaClosure.betaTraceClosesNegativeActiveConnectedNumerator
      dataSet directions laws actionTraceZero
      (asBetaTraceQuantumClosureInput input)
