{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySU2FiniteTraceClosureExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _<_)
import DASHI.Physics.Foundations.CMP119AntigravityQuantumTraceExact as Quantum
import DASHI.Physics.Foundations.CMP119AntigravityBetaTraceBridgeExact as BetaTrace
import DASHI.Physics.Foundations.CMP119AntigravityBetaTraceQuantumClosureExact as BetaClosure
import DASHI.Physics.Foundations.CMP119AntigravityFiniteHaarStrictPositivityExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravitySU2TraceConventionExact as SU2
import DASHI.Physics.Foundations.CMP119GibbsDiagonalTraceCancellationExact as Cancel
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- FINITE SU(2) TRACE CLOSURE
--
-- This removes the three independent strict-sign assumptions from the source
-- frontier.  Given an explicit finite Haar quadrature, one positive F^2
-- configuration witness, and the convention-correct same-object identity
--
--   Q_quantum = (-11/48) * N_{F^2,normalized},
--
-- the existing compilers derive:
--
--   Z > 0,
--   N_{F^2,normalized} > 0,
--   Q_quantum < 0,
--   C_active < 0.
--
-- The only physics that remains in this module is the SAME-OBJECT trace
-- identity itself and the finite quadrature/F^2 witness.
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

  record SU2FiniteTraceClosureInput : Set₁ where
    field
      traceAttachment :
        Quantum.RenormalizedTraceAttachment
          dataSet directions laws actionTraceZero

      quadrature :
        Strict.FiniteRationalHaarQuadrature measure

      normalizedFieldStrengthSquare :
        Configuration → ℚ

      fieldStrengthSquareWitness :
        Strict.PositiveFieldStrengthSquareWitness
          quadrature normalizedFieldStrengthSquare

      quantumTraceIsSU2BetaF2 :
        Quantum.quantumTraceNumerator
          dataSet directions laws actionTraceZero
          traceAttachment
        ≡
        SU2.su2TraceRationalCoefficient
        * Strict.fieldStrengthSquareNumerator
            quadrature normalizedFieldStrengthSquare

  open SU2FiniteTraceClosureInput public

  su2BetaTraceAttachment :
    (input : SU2FiniteTraceClosureInput) →
    BetaTrace.BetaTraceNumeratorAttachment
      (Quantum.quantumTraceNumerator
        dataSet directions laws actionTraceZero
        (traceAttachment input))
  su2BetaTraceAttachment input = record
    { BetaTrace.BetaTraceNumeratorAttachment.betaTraceCoefficient =
        SU2.su2TraceRationalCoefficient
    ; BetaTrace.BetaTraceNumeratorAttachment.fieldStrengthSquareNumerator =
        Strict.fieldStrengthSquareNumerator
          (quadrature input)
          (normalizedFieldStrengthSquare input)
    ; BetaTrace.BetaTraceNumeratorAttachment.selectedQuantumTraceIsBetaF2 =
        quantumTraceIsSU2BetaF2 input
    ; BetaTrace.BetaTraceNumeratorAttachment.betaTraceCoefficientNegative =
        SU2.su2TraceCoefficientNegative
    ; BetaTrace.BetaTraceNumeratorAttachment.fieldStrengthSquareNumeratorPositive =
        Strict.fieldStrengthSquareNumeratorPositive
          (quadrature input)
          (normalizedFieldStrengthSquare input)
          (fieldStrengthSquareWitness input)
    }

  asBetaTraceQuantumClosureInput :
    SU2FiniteTraceClosureInput →
    BetaClosure.BetaTraceQuantumClosureInput
      dataSet directions laws actionTraceZero
  asBetaTraceQuantumClosureInput input = record
    { BetaClosure.BetaTraceQuantumClosureInput.traceAttachment =
        traceAttachment input
    ; BetaClosure.BetaTraceQuantumClosureInput.partitionPositive =
        Strict.partitionFunctionPositive (quadrature input)
    ; BetaClosure.BetaTraceQuantumClosureInput.betaTraceAttachment =
        su2BetaTraceAttachment input
    }

  su2FiniteTraceClosesNegativeActiveConnectedNumerator :
    SU2FiniteTraceClosureInput →
    Quantum.activeConnectedNumerator
      dataSet directions laws actionTraceZero
    < 0ℚ
  su2FiniteTraceClosesNegativeActiveConnectedNumerator input =
    BetaClosure.betaTraceClosesNegativeActiveConnectedNumerator
      dataSet directions laws actionTraceZero
      (asBetaTraceQuantumClosureInput input)
