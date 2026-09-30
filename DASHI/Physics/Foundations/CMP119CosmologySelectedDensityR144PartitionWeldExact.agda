{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologySelectedDensityR144PartitionWeldExact where

------------------------------------------------------------------------
-- SAME SOURCE DENSITY -> SAME FINITE MEASURE -> SAME COMPLETE D1 -> DZ.
--
-- R124 already states that densityAt(k), after the explicit density->measure
-- map, is the literal finite measure Y(group, cutoffAtScale k).
-- The new cosmology R144 owner computes the complete-action partition
-- derivative on exactly such a PhysicalFiniteYMMeasure.
--
-- This module composes those facts. It prevents a cosmology calculation from
-- evaluating R144 D1 on one finite measure while claiming provenance from a
-- different CMP119 density.
--
-- Still conditional upstream:
--   * R124's literal density/measure weld must be instantiated physically;
--   * the finite action must be the selected complete CMP119 action;
--   * no continuum/renormalized/Lorentzian/FLRW theorem is inferred here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

import DASHI.Physics.Foundations.CMP119CosmologyR144CompleteActionPartitionResponseExact as R144Partition
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as R124
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact as R144Attach
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

module _
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    (composite : R144.CompositeStressFirstVariationInputs actionWeld laws)
    {G X Cutoff Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState : Set}
    where

  finiteAction : Finite.FiniteLocalizedEffectiveAction
  finiteAction = Carrier.finiteAction (Present.bc1Carrier present)

  Configuration : Set
  Configuration = Finite.Configuration finiteAction

  C : Top.LiteralYangMillsCarriers
  C =
    Physical.physicalLiteralCarriers
      G X Cutoff Configuration ℚ Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState

  module Selected
      {S : Top.LiteralYangMillsSemantics C}
      (Y : Top.LiteralYangMillsConstruction C S)
      (group : Top.CompactSimpleGroup C)
      {Scale Volume : Set}
      (domain :
        Domain.CanonicalMetricSourceDomain
          Scale Volume (R144.stressActivity composite))
      (representation : StressRep.CanonicalMetricStressRepresentation domain)
      {coordinate : R114.LiteralStressCoordinate Y group}
      (selected :
        R119.CanonicalMetricSelectedStressWeld
          domain representation coordinate)
      (attachment :
        R144Attach.R144CanonicalMetricTangentAttachment
          {trajectory = trajectory} {split = split} {inputs = inputs}
          {History = History} {Cell = Cell} {cutoff = cutoff}
          {present = present} {actionWeld = actionWeld} {laws = laws}
          composite
          {C = C} {S = S} {Y = Y} {group = group}
          {Scale = Scale} {Volume = Volume}
          domain representation {coordinate = coordinate} selected)
      (measureWeld :
        R124.BalabanDensityLiteralFiniteMeasureWeld
          {trajectory = trajectory} {split = split} {inputs = inputs}
          Y group)
      (scale : Nat)
      where

    selectedPhysicalMeasure :
      Physical.PhysicalFiniteYMMeasure Configuration ℚ
    selectedPhysicalMeasure =
      Top.finiteMeasure Y group
        (R124.cutoffAtScale measureWeld scale)

    sourceDensityMeasure :
      Physical.PhysicalFiniteYMMeasure Configuration ℚ
    sourceDensityMeasure =
      R124.densityToFiniteMeasure measureWeld
        (BetaDensity.densityAt inputs scale)

    sourceDensityIsSelectedPhysicalMeasure :
      sourceDensityMeasure ≡ selectedPhysicalMeasure
    sourceDensityIsSelectedPhysicalMeasure =
      R124.densityAtScaleIsLiteralFiniteMeasure measureWeld scale

    selectedPartitionDerivative :
      Finite.Tangent finiteAction → ℚ
    selectedPartitionDerivative =
      R144Partition.completeActionPartitionDerivative
        composite domain representation selected attachment
        selectedPhysicalMeasure

    sourceDensityPartitionDerivative :
      Finite.Tangent finiteAction → ℚ
    sourceDensityPartitionDerivative =
      R144Partition.completeActionPartitionDerivative
        composite domain representation selected attachment
        sourceDensityMeasure

    sourceDensityPartitionDerivativeIsSelected :
      ∀ tangent →
      sourceDensityPartitionDerivative tangent
      ≡ selectedPartitionDerivative tangent
    sourceDensityPartitionDerivativeIsSelected tangent =
      cong
        (λ measure →
          R144Partition.completeActionPartitionDerivative
            composite domain representation selected attachment
            measure tangent)
        sourceDensityIsSelectedPhysicalMeasure
