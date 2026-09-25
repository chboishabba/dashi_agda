{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119WilsonGibbsFiniteMeasureSameObjectExact where

open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119PhysicalFiniteMeasureNZDNDZExact as NZ
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact as FiniteSource
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- CANONICAL WILSON/GIBBS FINITE-MEASURE SAME-OBJECT CONSTRUCTOR
--
-- There is no need for a second independently supplied N/Z/DN/DZ calculus.
-- A ClassicalWilsonSelectedInsertion determines GibbsMetricInsertionData on
-- every literal finite measure; the existing Gibbs family adapter then
-- determines PhysicalRationalMetricStressData; the existing finite-source
-- adapter then determines the R121/R122 normalized finite-measure calculus.
--
-- Consequently the Wilson/Gibbs connected numerator and the finite-measure
-- source connected numerator are definitionally the same scalar.  The
-- remaining physical task is to anchor the actually selected CMP119 insertion
-- to THIS canonical constructor.
------------------------------------------------------------------------

module _
    {G X Cutoff Configuration Observable Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState : Set}
    where

  C : Top.LiteralYangMillsCarriers
  C =
    Physical.physicalLiteralCarriers
      G X Cutoff Configuration ℚ Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState

  wilsonGibbsFamily :
    Wilson.ClassicalWilsonSelectedInsertion Configuration →
    Gibbs.GibbsFiniteMeasureStressFamily
      {G = G} {X = X} {Cutoff = Cutoff}
      {Configuration = Configuration}
      {Observable = Observable} {Position = Position}
      {CurvaturePolynomial = CurvaturePolynomial}
      {LocalOperator = LocalOperator}
      {OPECoefficient = OPECoefficient}
      {StressTensor = StressTensor}
      {HilbertSpace = HilbertSpace}
      {Hamiltonian = Hamiltonian}
      {VacuumState = VacuumState}
      {MetricPerturbation = K.SymmetricTensorComponent4}
  wilsonGibbsFamily selectedInsertion = record
    { Gibbs.GibbsFiniteMeasureStressFamily.gibbsDataAt =
        λ measure →
          Wilson.asGibbsMetricInsertionData
            {measure = measure}
            selectedInsertion
    }

  wilsonPhysicalStressCalculus :
    Wilson.ClassicalWilsonSelectedInsertion Configuration →
    NZ.PhysicalRationalFiniteMeasureStressCalculus
      {G = G} {X = X} {Cutoff = Cutoff}
      {Configuration = Configuration}
      {Observable = Observable} {Position = Position}
      {CurvaturePolynomial = CurvaturePolynomial}
      {LocalOperator = LocalOperator}
      {OPECoefficient = OPECoefficient}
      {StressTensor = StressTensor}
      {HilbertSpace = HilbertSpace}
      {Hamiltonian = Hamiltonian}
      {VacuumState = VacuumState}
      K.SymmetricTensorComponent4
  wilsonPhysicalStressCalculus selectedInsertion =
    Gibbs.asPhysicalRationalFiniteMeasureStressCalculus
      (wilsonGibbsFamily selectedInsertion)

  module _
      {trajectory split}
      {inputs : Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split}}
      {S : Top.LiteralYangMillsSemantics C}
      {Y : Top.LiteralYangMillsConstruction C S}
      {group : Top.CompactSimpleGroup C}
      (measureWeld :
        R124.BalabanDensityLiteralFiniteMeasureWeld
          {trajectory = trajectory} {split = split} {inputs = inputs}
          Y group)
      (selectedInsertion :
        Wilson.ClassicalWilsonSelectedInsertion Configuration)
    where

    wilsonLiteralFiniteMeasureCalculus :
      FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus measureWeld
    wilsonLiteralFiniteMeasureCalculus =
      NZ.asLiteralFiniteMeasureNormalizedStressCalculus
        (wilsonPhysicalStressCalculus selectedInsertion)

    wilsonFiniteMeasureConnectedNumerator :
      Top.FiniteMeasure C →
      K.SymmetricTensorComponent4 →
      ℚ
    wilsonFiniteMeasureConnectedNumerator measure perturbation =
      NZ.connectedCrossNumerator
        (Gibbs.asPhysicalMetricStressData
          (Wilson.asGibbsMetricInsertionData
            {measure = measure}
            selectedInsertion))
        perturbation

    finiteMeasureCalculusIsWilsonGibbsConnectedNumerator :
      ∀ measure perturbation →
      FiniteSource.connectedInsertionNumerator
        wilsonLiteralFiniteMeasureCalculus
        measure perturbation
      ≡
      wilsonFiniteMeasureConnectedNumerator measure perturbation
    finiteMeasureCalculusIsWilsonGibbsConnectedNumerator
        measure perturbation =
      refl

    finiteMeasureNumeratorIsWilsonGibbsNumerator :
      ∀ measure →
      FiniteSource.numerator
        wilsonLiteralFiniteMeasureCalculus measure
      ≡
      NZ.numerator
        (Gibbs.asPhysicalMetricStressData
          (Wilson.asGibbsMetricInsertionData
            {measure = measure}
            selectedInsertion))
    finiteMeasureNumeratorIsWilsonGibbsNumerator measure = refl

    finiteMeasureDenominatorIsWilsonPartitionFunction :
      ∀ measure →
      FiniteSource.denominator
        wilsonLiteralFiniteMeasureCalculus measure
      ≡ Physical.partitionFunction measure
    finiteMeasureDenominatorIsWilsonPartitionFunction measure = refl

    finiteMeasureNumeratorDerivativeIsWilsonGibbs :
      ∀ measure perturbation →
      FiniteSource.numeratorDerivative
        wilsonLiteralFiniteMeasureCalculus measure perturbation
      ≡
      NZ.numeratorDerivative
        (Gibbs.asPhysicalMetricStressData
          (Wilson.asGibbsMetricInsertionData
            {measure = measure}
            selectedInsertion))
        perturbation
    finiteMeasureNumeratorDerivativeIsWilsonGibbs
        measure perturbation = refl

    finiteMeasureDenominatorDerivativeIsWilsonGibbs :
      ∀ measure perturbation →
      FiniteSource.denominatorDerivative
        wilsonLiteralFiniteMeasureCalculus measure perturbation
      ≡
      NZ.denominatorDerivative
        (Gibbs.asPhysicalMetricStressData
          (Wilson.asGibbsMetricInsertionData
            {measure = measure}
            selectedInsertion))
        perturbation
    finiteMeasureDenominatorDerivativeIsWilsonGibbs
        measure perturbation = refl
