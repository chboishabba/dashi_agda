{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedSourceTraceClosureExact where

open import Data.Rational.Base using (ℚ; 0ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonGibbsMinimalAnchorExact as Minimal
import DASHI.Physics.Foundations.CMP119AntigravityBetaTraceQuantumClosureExact as BetaClosure
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
-- SELECTED CMP119 SOURCE -> STRICT NEGATIVE ACTIVE TRACE
--
-- This is the current antigravity source capstone.  All representation and
-- coordinate plumbing is compiler-owned.  The remaining physical inputs are
-- visible in two records:
--
--   MinimalSelectedWilsonGibbsAnchor
--     one forall-over-slots connected-numerator same-object theorem;
--
--   BetaTraceQuantumClosureInput
--     selected trace = renormalized trace,
--     Z > 0,
--     renormalized trace numerator = beta * F^2 with the required signs.
--
-- The conclusion is strict negativity of the ACTUAL selected CMP119 diagonal
-- active sum.  No synthetic target tensor or off-diagonal evaluation is used.
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

    record SelectedCMP119TraceClosureInput : Set₁ where
      field
        sourceAnchor :
          Minimal.MinimalSelectedWilsonGibbsAnchor
            domain realization representation selected
            measureWeld wilsonInsertion

        integrationLaws :
          Integral.RationalFiniteMeasureIntegrationLaws
            (Minimal.selectedLiteralFiniteMeasure
              domain realization representation selected
              measureWeld wilsonInsertion
              sourceAnchor)

        betaTraceInput :
          BetaClosure.BetaTraceQuantumClosureInput
            (WilsonTrace.gibbsData
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion
                  sourceAnchor}
              wilsonInsertion integrationLaws)
            WilsonTrace.diagonalDirections
            integrationLaws
            (WilsonTrace.actionTraceZero
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion
                  sourceAnchor}
              wilsonInsertion integrationLaws)

    open SelectedCMP119TraceClosureInput public

    selectedCMP119DiagonalActiveSumNegative :
      (input : SelectedCMP119TraceClosureInput) →
      ∀ background →
      Minimal.selectedDiagonalActiveSum
        domain realization representation selected
        measureWeld wilsonInsertion
        background
      < 0ℚ
    selectedCMP119DiagonalActiveSumNegative input background =
      let
        anchor = sourceAnchor input
        laws = integrationLaws input

        activeNegative =
          BetaClosure.betaTraceClosesNegativeActiveConnectedNumerator
            (WilsonTrace.gibbsData
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion anchor}
              wilsonInsertion laws)
            WilsonTrace.diagonalDirections
            laws
            (WilsonTrace.actionTraceZero
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion anchor}
              wilsonInsertion laws)
            (betaTraceInput input)

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


------------------------------------------------------------------------
-- SU(2) SPECIALIZATION: STRICT SIGNS ARE NOW COMPILER OUTPUT
------------------------------------------------------------------------

module _
    {G X Cutoff Configuration Observable Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState : Set}
    where

  C₂ : Top.LiteralYangMillsCarriers
  C₂ =
    Physical.physicalLiteralCarriers
      G X Cutoff Configuration ℚ Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState

  module _
      {trajectory split}
      {inputs : Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split}}
      {S : Top.LiteralYangMillsSemantics C₂}
      {Y : Top.LiteralYangMillsConstruction C₂ S}
      {group : Top.CompactSimpleGroup C₂}
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

    record SelectedCMP119SU2TraceClosureInput : Set₁ where
      field
        sourceAnchor :
          Minimal.MinimalSelectedWilsonGibbsAnchor
            domain realization representation selected
            measureWeld wilsonInsertion

        integrationLaws :
          Integral.RationalFiniteMeasureIntegrationLaws
            (Minimal.selectedLiteralFiniteMeasure
              domain realization representation selected
              measureWeld wilsonInsertion
              sourceAnchor)

        su2FiniteTraceInput :
          SU2Finite.SU2FiniteTraceClosureInput
            (WilsonTrace.gibbsData
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion
                  sourceAnchor}
              wilsonInsertion integrationLaws)
            WilsonTrace.diagonalDirections
            integrationLaws
            (WilsonTrace.actionTraceZero
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion
                  sourceAnchor}
              wilsonInsertion integrationLaws)

    open SelectedCMP119SU2TraceClosureInput public

    selectedCMP119SU2DiagonalActiveSumNegative :
      (input : SelectedCMP119SU2TraceClosureInput) →
      ∀ background →
      Minimal.selectedDiagonalActiveSum
        domain realization representation selected
        measureWeld wilsonInsertion
        background
      < 0ℚ
    selectedCMP119SU2DiagonalActiveSumNegative input background =
      let
        anchor = sourceAnchor input
        laws = integrationLaws input

        activeNegative =
          SU2Finite.su2FiniteTraceClosesNegativeActiveConnectedNumerator
            (WilsonTrace.gibbsData
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion anchor}
              wilsonInsertion laws)
            WilsonTrace.diagonalDirections
            laws
            (WilsonTrace.actionTraceZero
              {measure =
                Minimal.selectedLiteralFiniteMeasure
                  domain realization representation selected
                  measureWeld wilsonInsertion anchor}
              wilsonInsertion laws)
            (su2FiniteTraceInput input)

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
