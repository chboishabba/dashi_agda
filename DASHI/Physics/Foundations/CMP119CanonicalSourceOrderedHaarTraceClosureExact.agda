{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CanonicalSourceOrderedHaarTraceClosureExact where

open import Data.Rational.Base using (ℚ; 0ℚ; _<_)

import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as Basis
import DASHI.Physics.Foundations.CMP119SymmetricWilsonGibbsAnchorConstructorExact as Anchor
import DASHI.Physics.Foundations.CMP119CanonicalWilsonGibbsMetricFamilyWeldCompilerExact as FamilyCompiler
import DASHI.Physics.Foundations.CMP119AntigravitySelectedMetricFamilyOrderedHaarClosureExact as Closure
import DASHI.Physics.Foundations.CMP119AntigravityOrderedHaarStrictPositivityExact as Ordered
import DASHI.Physics.Foundations.CMP119AntigravitySU2OrderedHaarTraceClosureExact as SU2Ordered
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTraceInsertionReductionExact as WilsonTrace
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- CANONICAL SELECTED SOURCE -> STRICT NEGATIVE FINITE DIAGONAL TRACE
--
-- The previous ordered-Haar capstone accepted a separately supplied
-- `SelectedMetricInsertionFamilyWilsonGibbsWeld`.  The new family compiler
-- proves that weld from the one source-facing equality
--
--   selected R119 normalized source = canonical Wilson/Gibbs cross data.
--
-- Thus this capstone charges only that equality plus the already-explicit Haar
-- and SU(2) trace inputs.  It proves the strict finite selected sign, but it does
-- NOT claim the stronger tail-beating cosmology margin.
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

  module _
      {trajectory split}
      {inputs : Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split}}
      {S : Top.LiteralYangMillsSemantics C}
      {Y : Top.LiteralYangMillsConstruction C S}
      {group : Top.CompactSimpleGroup C}
      {Scale Volume : Set}
      {activity : Chain.SubstitutedActivitySecondVariation}
      (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity)
      (realization : Basis.SymmetricMetricBasisRealization domain)
      (representation : StressRep.CanonicalMetricStressRepresentation domain)
      {coordinate : R114.LiteralStressCoordinate Y group}
      (selected :
        R119.CanonicalMetricSelectedStressWeld
          domain representation coordinate)
      (measureWeld :
        R124.BalabanDensityLiteralFiniteMeasureWeld
          {trajectory = trajectory} {split = split} {inputs = inputs}
          Y group)
      (wilsonInsertion :
        Wilson.ClassicalWilsonSelectedInsertion Configuration)
    where

    record CanonicalSourceOrderedHaarTraceInput : Set₂ where
      field
        sourceAnchor :
          Anchor.SelectedSourceCanonicalWilsonGibbsInput
            domain realization representation selected
            measureWeld wilsonInsertion

        orderedHaarLaws :
          Ordered.OrderedRationalHaarIntegrationLaws
            (FamilyCompiler.canonicalSelectedMeasure
              domain realization representation selected
              measureWeld wilsonInsertion sourceAnchor)

        su2OrderedTraceInput :
          SU2Ordered.SU2OrderedHaarTraceClosureInput
            (WilsonTrace.gibbsData
              {measure =
                FamilyCompiler.canonicalSelectedMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion sourceAnchor}
              wilsonInsertion
              (Ordered.linear orderedHaarLaws))
            WilsonTrace.diagonalDirections
            orderedHaarLaws
            (WilsonTrace.actionTraceZero
              {measure =
                FamilyCompiler.canonicalSelectedMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion sourceAnchor}
              wilsonInsertion
              (Ordered.linear orderedHaarLaws))

    open CanonicalSourceOrderedHaarTraceInput public

    asExistingOrderedHaarClosureInput :
      CanonicalSourceOrderedHaarTraceInput →
      Closure.SelectedMetricFamilyOrderedHaarClosureInput
        domain realization representation selected
        measureWeld wilsonInsertion
    asExistingOrderedHaarClosureInput input = record
      { Closure.SelectedMetricFamilyOrderedHaarClosureInput.metricFamilyWeld =
          FamilyCompiler.compileSelectedMetricInsertionFamilyWilsonGibbsWeld
            domain realization representation selected
            measureWeld wilsonInsertion
            (sourceAnchor input)
      ; Closure.SelectedMetricFamilyOrderedHaarClosureInput.orderedHaarLaws =
          orderedHaarLaws input
      ; Closure.SelectedMetricFamilyOrderedHaarClosureInput.su2OrderedTraceInput =
          su2OrderedTraceInput input
      }

    canonicalSourceDiagonalActiveSumNegative :
      (input : CanonicalSourceOrderedHaarTraceInput) →
      ∀ background →
      Closure.Minimal.selectedDiagonalActiveSum
        domain realization representation selected
        measureWeld wilsonInsertion
        background
      < 0ℚ
    canonicalSourceDiagonalActiveSumNegative input =
      Closure.selectedMetricFamilyOrderedHaarDiagonalActiveSumNegative
        domain realization representation selected
        measureWeld wilsonInsertion
        (asExistingOrderedHaarClosureInput input)
