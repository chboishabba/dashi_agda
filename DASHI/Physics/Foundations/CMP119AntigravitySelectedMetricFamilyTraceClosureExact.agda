{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedMetricFamilyTraceClosureExact where

open import Data.Rational.Base using (ℚ; _<_)
import DASHI.Physics.Foundations.CMP119SelectedMetricInsertionFamilyWilsonGibbsExact as Family
import DASHI.Physics.Foundations.CMP119AntigravitySelectedSourceTraceClosureExact as Closure
import DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonGibbsMinimalAnchorExact as Minimal
import DASHI.Physics.Foundations.CMP119AntigravitySU2FiniteTraceClosureExact as SU2Finite
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTraceInsertionReductionExact as WilsonTrace
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
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
-- CORRECT MULTI-SLOT SOURCE CAPSTONE
--
-- This is the preferred item-1 -> item-3 antigravity source theorem.
-- Unlike the historical scalar weld, the same-object insertion is indexed by
-- SymmetricTensorComponent4 and therefore does not collapse distinct stress
-- components.
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

    record SelectedMetricFamilySU2ClosureInput : Set₁ where
      field
        metricFamilyWeld :
          Family.SelectedMetricInsertionFamilyWilsonGibbsWeld
            domain realization representation selected
            measureWeld wilsonInsertion

        integrationLaws :
          Integral.RationalFiniteMeasureIntegrationLaws
            (Minimal.selectedLiteralFiniteMeasure
              domain realization representation selected
              measureWeld wilsonInsertion
              (Family.familyWeldToMinimalAnchor metricFamilyWeld))

        su2CurvatureTraceInput :
          SU2Finite.SU2CurvatureFiniteTraceClosureInput
            (WilsonTrace.gibbsData
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion
                  (Family.familyWeldToMinimalAnchor metricFamilyWeld)}
              wilsonInsertion integrationLaws)
            WilsonTrace.diagonalDirections
            integrationLaws
            (WilsonTrace.actionTraceZero
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion
                  (Family.familyWeldToMinimalAnchor metricFamilyWeld)}
              wilsonInsertion integrationLaws)

    open SelectedMetricFamilySU2ClosureInput public

    selectedMetricFamilyDiagonalActiveSumNegative :
      (input : SelectedMetricFamilySU2ClosureInput) →
      ∀ background →
      Minimal.selectedDiagonalActiveSum
        domain realization representation selected
        measureWeld wilsonInsertion
        background
      < 0ℚ
    selectedMetricFamilyDiagonalActiveSumNegative input background =
      let
        anchor =
          Family.familyWeldToMinimalAnchor
            (metricFamilyWeld input)
        laws = integrationLaws input
        closureInput :
          Closure.SelectedCMP119SU2TraceClosureInput
            domain realization representation selected
            measureWeld wilsonInsertion
        closureInput = record
          { Closure.SelectedCMP119SU2TraceClosureInput.sourceAnchor =
              anchor
          ; Closure.SelectedCMP119SU2TraceClosureInput.integrationLaws =
              laws
          ; Closure.SelectedCMP119SU2TraceClosureInput.su2FiniteTraceInput =
              su2CurvatureTraceInput input
          }
      in
      Closure.selectedCMP119SU2DiagonalActiveSumNegative
        domain realization representation selected
        measureWeld wilsonInsertion
        closureInput background
