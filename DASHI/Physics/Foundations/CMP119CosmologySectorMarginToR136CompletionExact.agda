{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologySectorMarginToR136CompletionExact where

------------------------------------------------------------------------
-- COMPOSE SOURCE SECTOR MARGIN (C) WITH ABSOLUTE EXPECTATION COMPLETION (B).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.Foundations.CMP119CosmologyNormalizedSectorWeylResponseExact as Normalized
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Completion
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

record FiniteGammaExpectationAnchor
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (source : R109.SourceNativeStressScaleCauchy)
    (completion : Completion.R144R109AbsoluteExpectationCompletion source)
    (scale : Nat)
    : Set₁ where
  field
    finiteExpectationIsGammaWeyl :
      Completion.finiteExpectation completion scale
      ≡ Convention.matterEffectiveActionWeylResponse measure partition d

open FiniteGammaExpectationAnchor public

normalizedSectorTailMarginForcesCompletedNegative :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation d h x ≡ 0ℚ)
    {source : R109.SourceNativeStressScaleCauchy}
    (completion : Completion.R144R109AbsoluteExpectationCompletion source)
    (scale : Nat)
    (anchor :
      FiniteGammaExpectationAnchor measure partition d source completion scale) →
  Normalized.normalizedNonWilsonWeylNumerator measure partition d
    + Completion.r109RemainingTail source scale < 0ℚ →
  Completion.completedExpectation completion < 0ℚ
normalizedSectorTailMarginForcesCompletedNegative
    {source = source}
    measure d laws partition referenceFixed completion scale anchor sectorTailMargin =
  let
    finiteMargin :
      Convention.matterEffectiveActionWeylResponse measure partition d
        + Completion.r109RemainingTail source scale < 0ℚ
    finiteMargin =
      Normalized.normalizedSectorMarginForcesFiniteGammaNegative
        measure d laws partition referenceFixed
        (Completion.r109RemainingTail source scale)
        sectorTailMargin

    anchoredMargin :
      Completion.finiteExpectation completion scale
        + Completion.r109RemainingTail source scale < 0ℚ
    anchoredMargin =
      subst
        (λ value →
          value + Completion.r109RemainingTail source scale < 0ℚ)
        (sym (finiteExpectationIsGammaWeyl anchor))
        finiteMargin
  in
  Completion.negativeFiniteMarginForcesNegativeCompletion
    completion scale anchoredMargin

sourceSignPlusTailNowControlsCompletedSign : Bool
sourceSignPlusTailNowControlsCompletedSign = true

remainingAbsoluteBridgeIsFiniteExpectationAnchor : Bool
remainingAbsoluteBridgeIsFiniteExpectationAnchor = true
