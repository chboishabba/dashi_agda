{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedMetricFamilyOrderedHaarClosureExact where

open import Data.Rational.Base using (ℚ; 0ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.CMP119SelectedMetricInsertionFamilyWilsonGibbsExact as Family
import DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonGibbsMinimalAnchorExact as Minimal
import DASHI.Physics.Foundations.CMP119AntigravityOrderedHaarStrictPositivityExact as Ordered
import DASHI.Physics.Foundations.CMP119AntigravitySU2OrderedHaarTraceClosureExact as SU2Ordered
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTraceInsertionReductionExact as WilsonTrace
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as Basis
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
-- PREFERRED ITEMS 1--3 CAPSTONE
--
-- This theorem uses:
--   (1) a metric-slot-indexed CMP119 -> Wilson/Gibbs same-object family;
--   (2) the actual ordered Haar functional, not an exact finite quadrature;
--   (3) an explicit scalar 1/pi^2 normalization weld inside the SU2 closure.
--
-- It concludes strict negativity of the selected CMP119 diagonal active sum.
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

    record SelectedMetricFamilyOrderedHaarClosureInput : Set₂ where
      field
        metricFamilyWeld :
          Family.SelectedMetricInsertionFamilyWilsonGibbsWeld
            domain realization representation selected
            measureWeld wilsonInsertion

        orderedHaarLaws :
          Ordered.OrderedRationalHaarIntegrationLaws
            (Minimal.selectedLiteralFiniteMeasure
              domain realization representation selected
              measureWeld wilsonInsertion
              (Family.familyWeldToMinimalAnchor metricFamilyWeld))

        su2OrderedTraceInput :
          SU2Ordered.SU2OrderedHaarTraceClosureInput
            (WilsonTrace.gibbsData
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion
                  (Family.familyWeldToMinimalAnchor metricFamilyWeld)}
              wilsonInsertion
              (Ordered.linear orderedHaarLaws))
            WilsonTrace.diagonalDirections
            orderedHaarLaws
            (WilsonTrace.actionTraceZero
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion
                  (Family.familyWeldToMinimalAnchor metricFamilyWeld)}
              wilsonInsertion
              (Ordered.linear orderedHaarLaws))

    open SelectedMetricFamilyOrderedHaarClosureInput public

    selectedMetricFamilyOrderedHaarDiagonalActiveSumNegative :
      (input : SelectedMetricFamilyOrderedHaarClosureInput) →
      ∀ background →
      Minimal.selectedDiagonalActiveSum
        domain realization representation selected
        measureWeld wilsonInsertion
        background
      < 0ℚ
    selectedMetricFamilyOrderedHaarDiagonalActiveSumNegative input background =
      let
        anchor =
          Family.familyWeldToMinimalAnchor
            (metricFamilyWeld input)

        ordered =
          orderedHaarLaws input

        laws =
          Ordered.linear ordered

        activeNegative =
          SU2Ordered.su2OrderedHaarTraceClosesNegativeActiveConnectedNumerator
            (WilsonTrace.gibbsData
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion anchor}
              wilsonInsertion laws)
            WilsonTrace.diagonalDirections
            ordered
            (WilsonTrace.actionTraceZero
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion anchor}
              wilsonInsertion laws)
            (su2OrderedTraceInput input)

        wilsonNegative =
          subst
            (λ value → value < 0ℚ)
            (sym
              (Minimal.wilsonDiagonalActiveSumIsTraceActiveConnectedNumerator
                domain realization representation selected
                measureWeld wilsonInsertion
                anchor laws))
            activeNegative
      in
      subst
        (λ value → value < 0ℚ)
        (sym
          (Minimal.selectedDiagonalActiveSumIsWilsonDiagonalActiveSum
            domain realization representation selected
            measureWeld wilsonInsertion
            anchor background))
        wilsonNegative
