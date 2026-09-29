{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SelectedFiniteTraceSilenceNoGoExact where

------------------------------------------------------------------------
-- Selected CMP119 -> literal Wilson/Gibbs finite measure -> trace necessity.
--
-- This is the same-physical-measure specialization of the generic finite
-- trace-silent insertion no-go. No new trace sign premise or fitting
-- parameter is inserted. The existing source attachment is consumed at
-- the *selected* beta density/cutoff, not at a separate synthetic measure.
--
-- Negative selected connected diagonal sum implies that the selected
-- Wilson insertion must have a nonzero pointwise diagonal variation
-- somewhere on its selected Configuration carrier.
--
-- It does NOT prove that an anomaly actually occurs, nor construct the
-- needed continuum renormalized quantum stress.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ; 0ℚ; _<_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as Basis
import DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonGibbsMinimalAnchorExact as Minimal
import DASHI.Physics.Foundations.CMP119WilsonGibbsVanishingInsertionTraceNoGoExact as Silent
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTraceInsertionReductionExact as Trace
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

module _
    {G X Cutoff Configuration Observable Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState : Set}
    where

  C : Top.LiteralYangMillsCarriers
  C = Physical.physicalLiteralCarriers
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

    SelectedAnchor :
      Set₁
    SelectedAnchor =
      Minimal.MinimalSelectedWilsonGibbsAnchor
        domain realization representation selected
        measureWeld wilsonInsertion

    selectedMeasure :
      SelectedAnchor → Physical.PhysicalFiniteYMMeasure Configuration ℚ
    selectedMeasure anchor =
      Minimal.selectedLiteralFiniteMeasure
        domain realization representation selected
        measureWeld wilsonInsertion anchor

    selectedActiveIsHaarActive :
      (anchor : SelectedAnchor)
      (laws : Integral.RationalFiniteMeasureIntegrationLaws
        (selectedMeasure anchor))
      (background : Chain.Background activity) →
      Minimal.selectedDiagonalActiveSum
        domain realization representation selected
        measureWeld wilsonInsertion background
      ≡
      Trace.activeConnectedNumerator
        {measure = selectedMeasure anchor}
        wilsonInsertion laws
    selectedActiveIsHaarActive anchor laws background =
      trans
        (Minimal.selectedDiagonalActiveSumIsWilsonDiagonalActiveSum
          domain realization representation selected
          measureWeld wilsonInsertion anchor background)
        (Minimal.wilsonDiagonalActiveSumIsTraceActiveConnectedNumerator
          domain realization representation selected
          measureWeld wilsonInsertion anchor laws)

    traceSilenceForcesSelectedActiveZero :
      (anchor : SelectedAnchor)
      (laws : Integral.RationalFiniteMeasureIntegrationLaws
        (selectedMeasure anchor))
      (silent : Silent.TraceSilentInsertion
        {measure = selectedMeasure anchor}
        wilsonInsertion laws)
      (background : Chain.Background activity) →
      Minimal.selectedDiagonalActiveSum
        domain realization representation selected
        measureWeld wilsonInsertion background
      ≡ 0ℚ
    traceSilenceForcesSelectedActiveZero anchor laws silent background =
      trans
        (selectedActiveIsHaarActive anchor laws background)
        (Silent.selectedConnectedActiveSumZero
          {measure = selectedMeasure anchor}
          wilsonInsertion laws silent)

    selectedNegativeActiveRequiresTraceVariation :
      (anchor : SelectedAnchor)
      (laws : Integral.RationalFiniteMeasureIntegrationLaws
        (selectedMeasure anchor))
      (background : Chain.Background activity) →
      Minimal.selectedDiagonalActiveSum
        domain realization representation selected
        measureWeld wilsonInsertion background < 0ℚ →
      Silent.TraceSilentInsertion
        {measure = selectedMeasure anchor}
        wilsonInsertion laws →
      ⊥
    selectedNegativeActiveRequiresTraceVariation
        anchor laws background negative silent =
      Silent.selectedNegativeActiveRulesOutTraceSilence
        {measure = selectedMeasure anchor}
        wilsonInsertion laws
        (subst
          (λ value → value < 0ℚ)
          (selectedActiveIsHaarActive anchor laws background)
          negative)
        silent
