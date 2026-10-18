{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119GibbsDiagonalTraceSignExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119GibbsDiagonalTraceCancellationExact as Cancel
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- STRICT SIGN COROLLARY
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

  traceInsertionNumerator =
    Cancel.traceInsertionNumerator
      dataSet directions laws actionTraceZero

  activeConnectedNumerator =
    Cancel.activeConnectedNumerator
      dataSet directions laws actionTraceZero

  record PositivePartitionNegativeTraceInput : Set where
    field
      partitionPositive :
        0ℚ < Physical.partitionFunction measure

      traceInsertionNegative :
        traceInsertionNumerator < 0ℚ

  open PositivePartitionNegativeTraceInput public

  partitionTimesTraceNegative :
    PositivePartitionNegativeTraceInput →
    Physical.partitionFunction measure * traceInsertionNumerator < 0ℚ
  partitionTimesTraceNegative input =
    let
      z = Physical.partitionFunction measure

      instance
        zPositive : Positive z
        zPositive = positive (partitionPositive input)

      scaled :
        z * traceInsertionNumerator < z * 0ℚ
      scaled =
        ℚP.*-monoˡ-<-pos z (traceInsertionNegative input)
    in
    subst
      (λ right → z * traceInsertionNumerator < right)
      (ℚRing.solve-∀ z)
      scaled

  activeConnectedNumeratorNegative :
    PositivePartitionNegativeTraceInput →
    activeConnectedNumerator < 0ℚ
  activeConnectedNumeratorNegative input =
    subst
      (λ left → left < 0ℚ)
      (Relation.Binary.PropositionalEquality.sym
        (Cancel.activeConnectedNumeratorIsPartitionTimesTraceInsertion
          dataSet directions laws actionTraceZero))
      (partitionTimesTraceNegative input)
