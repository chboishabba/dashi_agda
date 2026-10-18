{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ClassicalWilsonTraceInsertionReductionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _<_)
import Relation.Binary.PropositionalEquality as Eq

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.Foundations.CMP119GibbsDiagonalTraceCancellationExact as Cancel
import DASHI.Physics.Foundations.CMP119GibbsDiagonalTraceSignExact as Sign
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- CLASSICAL WILSON SPECIALIZATION
--
-- The four diagonal directions are fixed canonically.  The classical action
-- trace vanishes pointwise, so the active connected numerator depends only on
-- the trace of the INSERTION variation.
------------------------------------------------------------------------

diagonalDirections :
  Cancel.FourDiagonalPerturbations K.SymmetricTensorComponent4
diagonalDirections = record
  { Cancel.FourDiagonalPerturbations.h00 = K.component00
  ; Cancel.FourDiagonalPerturbations.h11 = K.component11
  ; Cancel.FourDiagonalPerturbations.h22 = K.component22
  ; Cancel.FourDiagonalPerturbations.h33 = K.component33
  }

module _
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (selectedInsertion : Wilson.ClassicalWilsonSelectedInsertion Configuration)
    (laws : Integral.RationalFiniteMeasureIntegrationLaws measure)
  where

  gibbsData :
    Gibbs.GibbsMetricInsertionData
      Configuration K.SymmetricTensorComponent4 measure
  gibbsData =
    Wilson.asGibbsMetricInsertionData selectedInsertion

  actionTraceZero :
    ∀ configuration →
    Gibbs.actionVariation gibbsData K.component00 configuration
    + Gibbs.actionVariation gibbsData K.component11 configuration
    + Gibbs.actionVariation gibbsData K.component22 configuration
    + Gibbs.actionVariation gibbsData K.component33 configuration
    ≡ 0ℚ
  actionTraceZero configuration =
    Wilson.diagonalActionVariationTraceZero
      (Wilson.actionMetricVariation selectedInsertion)
      configuration

  traceInsertionVariation : Configuration → ℚ
  traceInsertionVariation =
    Cancel.traceInsertionVariation
      gibbsData diagonalDirections laws actionTraceZero

  traceInsertionNumerator : ℚ
  traceInsertionNumerator =
    Cancel.traceInsertionNumerator
      gibbsData diagonalDirections laws actionTraceZero

  activeConnectedNumerator : ℚ
  activeConnectedNumerator =
    Cancel.activeConnectedNumerator
      gibbsData diagonalDirections laws actionTraceZero

  activeConnectedNumeratorIsPartitionTimesTraceInsertion :
    activeConnectedNumerator
    ≡ Physical.partitionFunction measure * traceInsertionNumerator
  activeConnectedNumeratorIsPartitionTimesTraceInsertion =
    Cancel.activeConnectedNumeratorIsPartitionTimesTraceInsertion
      gibbsData diagonalDirections laws actionTraceZero

  record NegativeQuantumTraceInput : Set where
    field
      partitionPositive :
        0ℚ < Physical.partitionFunction measure

      traceInsertionNegative :
        traceInsertionNumerator < 0ℚ

  open NegativeQuantumTraceInput public

  negativeQuantumTraceGivesNegativeActiveConnectedNumerator :
    NegativeQuantumTraceInput →
    activeConnectedNumerator < 0ℚ
  negativeQuantumTraceGivesNegativeActiveConnectedNumerator input =
    Sign.activeConnectedNumeratorNegative
      gibbsData diagonalDirections laws actionTraceZero
      (record
        { Sign.PositivePartitionNegativeTraceInput.partitionPositive =
            partitionPositive input
        ; Sign.PositivePartitionNegativeTraceInput.traceInsertionNegative =
            traceInsertionNegative input
        })
