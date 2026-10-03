{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1R144DirectMarkedCompilerExact where

------------------------------------------------------------------------
-- R143 LOCALIZED D1 COVARIANCE + R144 SAME-STRESS IDENTIFICATION -> MARKED E1.
--
-- The old R133 E1 route asked the auxiliary background/tangent transport maps
-- to commute with the Euclidean action.  That is unnecessary on the shortest
-- same-object route:
--
--   R143: BC2 global D1 = finite localized D1 sum
--   R144: selected stress D1 = the SAME finite localized D1 sum
--
-- Marked E1 can therefore use the global BC2 derivative directly, with R144 as
-- the same-stress provenance theorem.  No equivariance theorem for R133's
-- internal transport maps is a premise of this compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE1DifferentiatedCovarianceExact as MarkedE1
import DASHI.Physics.Foundations.CMP119CosmologyE1LocalizedD1CovarianceExact as LocalE1
import DASHI.Physics.Foundations.CMP119CosmologyE1R143LocalizedCompilerExact as R143E1

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144

record R144DirectMarkedE1
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    (laws : R143.PresentCutBC2FirstVariationLinearity present)
    (stress : R144.CompositeStressFirstVariationInputs actionWeld laws)
    (EuclideanAction : Set)
    : Set₁ where
  field
    localizedCovariance :
      R143E1.R143LocalizedEuclideanCovariance present laws EuclideanAction

open R144DirectMarkedE1 public

asDifferentiatedEuclideanCovariance :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws stress
      EuclideanAction} →
  R144DirectMarkedE1
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld}
    laws stress EuclideanAction →
  MarkedE1.DifferentiatedEuclideanCovariance
    EuclideanAction
    (Carrier.Configuration (Present.bc1Carrier present))
    (Carrier.Tangent (Present.bc1Carrier present))
    ℝ
asDifferentiatedEuclideanCovariance
    {present = present} dataSet = record
  { MarkedE1.DifferentiatedEuclideanCovariance.actBase =
      LocalE1.actConfiguration
        (R143E1.localized (localizedCovariance dataSet))
  ; MarkedE1.DifferentiatedEuclideanCovariance.actStress =
      LocalE1.actTangent
        (R143E1.localized (localizedCovariance dataSet))
  ; MarkedE1.DifferentiatedEuclideanCovariance.baseExpectation =
      Carrier.effectivePotential (Present.bc1Carrier present)
  ; MarkedE1.DifferentiatedEuclideanCovariance.markedDerivative =
      BC2.firstVariation (Present.bc2 present)
        (Carrier.effectivePotential (Present.bc1Carrier present))
  ; MarkedE1.DifferentiatedEuclideanCovariance.baseCovariant =
      λ action background →
        LocalE1.cmp109EffectivePotentialCovariant
          (R143E1.localized (localizedCovariance dataSet))
          action background
  ; MarkedE1.DifferentiatedEuclideanCovariance.derivativeEquivariant =
      R143E1.bc2FirstVariationCovariantFromLocalizedD1
        (localizedCovariance dataSet)
  }

------------------------------------------------------------------------
-- Same-stress provenance.
--
-- The R144 datum is intentionally retained in this record even though the E1
-- covariance proof itself consumes only the global/finite equality.  Its
-- `stressFirstVariationIsFiniteLocalizedSum` field is exactly the theorem that
-- identifies the finite D1 mark above with the selected stress first variation.
------------------------------------------------------------------------

r144SameStressProvenanceAvailable :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws stress
      EuclideanAction}
    (dataSet :
      R144DirectMarkedE1
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} {actionWeld = actionWeld}
        laws stress EuclideanAction) →
  R144.CompositeStressFirstVariationInputs actionWeld laws
r144SameStressProvenanceAvailable {stress = stress} dataSet = stress

markedE1NoLongerNeedsR133TransportEquivariance : Bool
markedE1NoLongerNeedsR133TransportEquivariance = true

r133BackgroundTransportEquivarianceStillMarkedE1Premise : Bool
r133BackgroundTransportEquivarianceStillMarkedE1Premise = false

r133TangentTransportEquivarianceStillMarkedE1Premise : Bool
r133TangentTransportEquivarianceStillMarkedE1Premise = false

remainingMarkedE1NovelLeavesAreLocalizedComponentGeometryAndDerivativeNaturality : Bool
remainingMarkedE1NovelLeavesAreLocalizedComponentGeometryAndDerivativeNaturality = true
