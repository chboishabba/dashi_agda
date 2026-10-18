{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SelectedWilsonGibbsAnchorExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

import DASHI.Physics.Foundations.CMP119WilsonGibbsFiniteMeasureSameObjectExact as Same
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact as FiniteSource
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureDensityAnchorConstructorExact as Anchor
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.Foundations.CMP119PhysicalFiniteMeasureNZDNDZExact as NZ
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact as R122
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- SELECTED CMP119 -> CANONICAL WILSON/GIBBS SAME-OBJECT WELD
--
-- The previous file makes the Wilson/Gibbs N/Z/DN/DZ calculus canonical.
-- Here we consume the ordinary R122 selected-density anchor with THAT calculus.
-- Therefore, once the selected CMP119 normalized source is anchored to the
-- canonical calculus, its connected insertion numerator is literally the
-- Wilson/Gibbs connected numerator on the same selected finite measure.
--
-- No target stress values or trace sign are assumed.
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
      {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
      {representation : StressRep.CanonicalMetricStressRepresentation domain}
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

    canonicalCalculus :
      FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus measureWeld
    canonicalCalculus =
      Same.wilsonLiteralFiniteMeasureCalculus
        measureWeld wilsonInsertion

    record SelectedWilsonGibbsAnchor : Set₁ where
      field
        anchorInputs :
          Anchor.LiteralFiniteMeasureDensityAnchorInputs
            {trajectory = trajectory} {split = split} {inputs = inputs}
            {C = C} {S = S} {Y = Y} {group = group}
            {Scale = Scale} {Volume = Volume}
            {activity = activity}
            {domain = domain} {representation = representation}
            {coordinate = coordinate}
            selected measureWeld canonicalCalculus

    open SelectedWilsonGibbsAnchor public

    selectedScaleIndex :
      SelectedWilsonGibbsAnchor → Nat
    selectedScaleIndex anchor =
      Anchor.sourceScaleIndex (anchorInputs anchor)
        (Anchor.selectedScale (anchorInputs anchor))

    selectedLiteralFiniteMeasure :
      SelectedWilsonGibbsAnchor →
      Top.FiniteMeasure C
    selectedLiteralFiniteMeasure anchor =
      Top.finiteMeasure Y group
        (R124.cutoffAtScale measureWeld (selectedScaleIndex anchor))

    selectedWilsonPerturbation :
      SelectedWilsonGibbsAnchor →
      Domain.MetricPerturbation domain →
      K.SymmetricTensorComponent4
    selectedWilsonPerturbation anchor perturbation =
      Anchor.metricPerturbationToFiniteMeasurePerturbation
        (anchorInputs anchor) perturbation

    selectedCMP119ConnectedNumerator :
      Chain.Background activity →
      Domain.MetricPerturbation domain →
      ℚ
    selectedCMP119ConnectedNumerator background perturbation =
      R116.connectedInsertionNumerator
        (R119.normalizedSource selected background perturbation)

    selectedWilsonGibbsConnectedNumerator :
      SelectedWilsonGibbsAnchor →
      Domain.MetricPerturbation domain →
      ℚ
    selectedWilsonGibbsConnectedNumerator anchor perturbation =
      NZ.connectedCrossNumerator
        (Gibbs.asPhysicalMetricStressData
          (Wilson.asGibbsMetricInsertionData
            {measure = selectedLiteralFiniteMeasure anchor}
            wilsonInsertion))
        (selectedWilsonPerturbation anchor perturbation)

    selectedCMP119ConnectedNumeratorIsWilsonGibbs :
      (anchor : SelectedWilsonGibbsAnchor) →
      ∀ background perturbation →
      selectedCMP119ConnectedNumerator background perturbation
      ≡ selectedWilsonGibbsConnectedNumerator anchor perturbation
    selectedCMP119ConnectedNumeratorIsWilsonGibbs
        anchor background perturbation =
      let
        scale = selectedScaleIndex anchor
        finitePerturbation =
          selectedWilsonPerturbation anchor perturbation
        densityAnchor =
          Anchor.asDensityAnchoredCanonicalMetricStress
            (anchorInputs anchor)
      in
      trans
        (R122.canonicalMetricConnectedInsertionIsOnLiteralDensity
          densityAnchor background perturbation)
        (trans
          (FiniteSource.connectedNumeratorAtBetaScaleIsFiniteMeasureNumerator
            canonicalCalculus scale finitePerturbation)
          (Same.finiteMeasureCalculusIsWilsonGibbsConnectedNumerator
            measureWeld wilsonInsertion
            (selectedLiteralFiniteMeasure anchor)
            finitePerturbation))
