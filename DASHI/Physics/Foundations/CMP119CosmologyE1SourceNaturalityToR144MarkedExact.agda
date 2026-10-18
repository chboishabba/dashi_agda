{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1SourceNaturalityToR144MarkedExact where

------------------------------------------------------------------------
-- SOURCE DERIVATIVE NATURALITY -> DIRECT R144 MARKED E1.
--
-- The source-local naturality record already contains the exact component
-- permutation/local-activity covariance needed to derive every local D1 law.
-- The component-permutation compiler pays finite reindexing, R143 pays the
-- global finite sum, and the direct R144 compiler uses the same finite D1 sum
-- as stress provenance.  R133 transport equivariance is not charged.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyE1ComponentPermutationExact as PermE1
import DASHI.Physics.Foundations.CMP119CosmologyE1R143LocalizedCompilerExact as R143E1
import DASHI.Physics.Foundations.CMP119CosmologyE1R144DirectMarkedCompilerExact as R144Direct
import DASHI.Physics.Foundations.CMP119CosmologyE1SourceDerivativeNaturalityExact as SourceE1

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132

fromLiteralSourceDerivativeNaturality :
  ∀ {History Cell : Set} {cutoff : Nat}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    {EuclideanAction : Set} →
  SourceE1.LiteralSourceDerivativeNaturality
    (Present.bc1Carrier present)
    (R143.asFirstVariationLinearity laws)
    EuclideanAction →
  R143E1.R143LocalizedEuclideanCovariance present laws EuclideanAction
fromLiteralSourceDerivativeNaturality naturality = record
  { R143E1.R143LocalizedEuclideanCovariance.localized =
      PermE1.asLocalizedD1EuclideanCovariance
        (SourceE1.asComponentPermutationCovariance naturality)
  }

sourceNaturalityToDirectR144MarkedE1 :
  ∀ {History Cell : Set} {cutoff : Nat}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    {stress : R144.CompositeStressFirstVariationInputs actionWeld laws}
    {EuclideanAction : Set} →
  SourceE1.LiteralSourceDerivativeNaturality
    (Present.bc1Carrier present)
    (R143.asFirstVariationLinearity laws)
    EuclideanAction →
  R144Direct.R144DirectMarkedE1 laws stress EuclideanAction
sourceNaturalityToDirectR144MarkedE1 naturality = record
  { R144Direct.R144DirectMarkedE1.localizedCovariance =
      fromLiteralSourceDerivativeNaturality naturality
  }

sourceDerivativeNaturalityCompilesToR143LocalizedCovariance : Bool
sourceDerivativeNaturalityCompilesToR143LocalizedCovariance = true

r133TransportEquivarianceRequiredForDirectMarkedA1 : Bool
r133TransportEquivarianceRequiredForDirectMarkedA1 = false

independentPerComponentD1CovarianceRequired : Bool
independentPerComponentD1CovarianceRequired = false

remainingA1ProducerDataIsLiteralSourceNaturalityAndGeometry : Bool
remainingA1ProducerDataIsLiteralSourceNaturalityAndGeometry = true
