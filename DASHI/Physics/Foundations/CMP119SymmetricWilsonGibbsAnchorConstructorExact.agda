{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricWilsonGibbsAnchorConstructorExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as Basis
import DASHI.Physics.Foundations.CMP119SymmetricCanonicalMetricRechartExact as Rechart
import DASHI.Physics.Foundations.CMP119WilsonGibbsFiniteMeasureSameObjectExact as Same
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact as FiniteSource
import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureDensityAnchorConstructorExact as Anchor
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanLiteralDensityNormalizedSourceRound121Exact as R121
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- RECHARTED SELECTED SOURCE -> CANONICAL WILSON/GIBBS ANCHOR
--
-- After recharting Round106/R119 onto SymmetricTensorComponent4, the canonical
-- Wilson/Gibbs finite-measure calculus uses the SAME perturbation carrier.
-- Therefore the R122 metric->finite-measure perturbation map is identity.
--
-- Remaining physical input:
--   selected normalized CMP119 source
--     = canonical Wilson/Gibbs finite-measure cross-data
-- at the selected Balaban scale.
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

    rechartedDomain =
      Rechart.symmetricDomain domain realization

    rechartedRepresentation =
      Rechart.symmetricRepresentation domain realization representation

    rechartedSelected =
      Rechart.rechartedSelectedStress
        domain realization representation selected

    canonicalCalculus :
      FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus measureWeld
    canonicalCalculus =
      Same.wilsonLiteralFiniteMeasureCalculus
        measureWeld wilsonInsertion

    record SelectedSourceCanonicalWilsonGibbsInput : Set₁ where
      field
        selectedScale : Scale
        sourceScaleIndex : Scale → Nat

        selectedNormalizedSourceIsCanonicalWilsonGibbs :
          ∀ background component →
          R119.normalizedSource
            rechartedSelected background component
          ≡
          R121.crossDataAt
            (FiniteSource.asLiteralDensityNormalizedStressSource
              canonicalCalculus)
            (sourceScaleIndex selectedScale)
            component

    open SelectedSourceCanonicalWilsonGibbsInput public

    asLiteralFiniteMeasureDensityAnchorInputs :
      SelectedSourceCanonicalWilsonGibbsInput →
      Anchor.LiteralFiniteMeasureDensityAnchorInputs
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume}
        {activity = activity}
        {domain = rechartedDomain}
        {representation = rechartedRepresentation}
        {coordinate = coordinate}
        rechartedSelected measureWeld canonicalCalculus
    asLiteralFiniteMeasureDensityAnchorInputs input = record
      { Anchor.LiteralFiniteMeasureDensityAnchorInputs.selectedScale =
          selectedScale input
      ; Anchor.LiteralFiniteMeasureDensityAnchorInputs.sourceScaleIndex =
          sourceScaleIndex input
      ; Anchor.LiteralFiniteMeasureDensityAnchorInputs.metricPerturbationToFiniteMeasurePerturbation =
          λ component → component
      ; Anchor.LiteralFiniteMeasureDensityAnchorInputs.selectedNormalizedSourceIsFiniteMeasureSource =
          selectedNormalizedSourceIsCanonicalWilsonGibbs input
      }

    finiteMeasurePerturbationRoundTripIsIdentity :
      (input : SelectedSourceCanonicalWilsonGibbsInput) →
      ∀ component →
      Anchor.metricPerturbationToFiniteMeasurePerturbation
        (asLiteralFiniteMeasureDensityAnchorInputs input)
        component
      ≡ component
    finiteMeasurePerturbationRoundTripIsIdentity input component =
      refl
