{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedJApplicabilityRound309Exact where

------------------------------------------------------------------------
-- ROUND309 / PUBLISHED CMP116 J-LOCALIZATION vs SELECTED-T5 APPLICABILITY
--
-- R296/R299/R306 already identify the preferred B-side source payment as
--
--   |D^2_{J_A,J_B} log Z| <= rooted connecting shell.
--
-- The proof-search correction here is to split that statement into two typed
-- coordinates:
--
--   (1) a SOURCE authority on the literal declared CMP116 J carrier;
--   (2) a SAME-OBJECT/APPLICABILITY weld identifying the selected physical T5
--       mixed derivative, support distance and connecting root with that source
--       carrier.
--
-- The source authority is indexed by the exact T5 scale/volume/root/J carrier
-- and its exact shellData.  Therefore carrier-type equality is not enough to
-- pay G1: a theorem on a neighbouring shell presentation cannot be transported
-- silently into the selected physical consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source

------------------------------------------------------------------------
-- Typed published/source localization on the EXACT selected-T5 carrier.
------------------------------------------------------------------------

record PublishedTwoJLocalizationForT5
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (presentation : R295.DirectT5StateFamilyJPresentation dataSet extension)
    : Set₁ where
  field
    sourceMagnitude :
      R295.Scale presentation →
      R295.Volume presentation →
      R295.SourceDirection presentation →
      R295.SourceDirection presentation → ℚ

    sourceRoot :
      R295.Scale presentation →
      R295.Volume presentation →
      R295.SourceDirection presentation →
      R295.SourceDirection presentation →
      R295.Root presentation

    sourceDistance :
      R295.SourceDirection presentation →
      R295.SourceDirection presentation → Nat

    -- This is the source theorem on its declared J directions.  No selected-T5
    -- applicability is hidden in this field.
    localized : ∀ scale volume left right →
      sourceMagnitude scale volume left right
      ≤ Shell.rootedShell (R295.shellData presentation)
          scale volume
          (sourceRoot scale volume left right)
          (sourceDistance left right)

open PublishedTwoJLocalizationForT5 public

------------------------------------------------------------------------
-- Same-object selected-T5 applicability only.
------------------------------------------------------------------------

record SelectedT5JApplicability
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (presentation : R295.DirectT5StateFamilyJPresentation dataSet extension)
    (published : PublishedTwoJLocalizationForT5 presentation)
    : Set₁ where
  field
    sourceMagnitudeIsSelectedMixedDerivativeAbsolute :
      ∀ cutoff left right →
      sourceMagnitude published
        (R295.scaleOf presentation cutoff)
        (R295.volumeOf presentation cutoff)
        (Cumulant.sourceDirectionOf (R295.meaning presentation) left)
        (Cumulant.sourceDirectionOf (R295.meaning presentation) right)
      ≡
      ∣ Cumulant.literalMixedSecondLogDerivative
          (R295.meaning presentation)
          (Cumulant.sourceDirectionOf (R295.meaning presentation) left)
          (Cumulant.sourceDirectionOf (R295.meaning presentation) right)
          cutoff ∣

    sourceRootIsSelectedConnectingRoot :
      ∀ cutoff left right →
      sourceRoot published
        (R295.scaleOf presentation cutoff)
        (R295.volumeOf presentation cutoff)
        (Cumulant.sourceDirectionOf (R295.meaning presentation) left)
        (Cumulant.sourceDirectionOf (R295.meaning presentation) right)
      ≡ R295.connectingRoot presentation cutoff left right

    sourceDistanceIsSelectedPhysicalDistance :
      ∀ left right →
      sourceDistance published
        (Cumulant.sourceDirectionOf (R295.meaning presentation) left)
        (Cumulant.sourceDirectionOf (R295.meaning presentation) right)
      ≡ R295.physicalDistance presentation left right

open SelectedT5JApplicability public

------------------------------------------------------------------------
-- Compiler into the exact current G1 consumer.
------------------------------------------------------------------------

selectedT5AbsoluteLocalization :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {presentation : R295.DirectT5StateFamilyJPresentation dataSet extension}
    {published : PublishedTwoJLocalizationForT5 presentation} →
  SelectedT5JApplicability presentation published →
  ∀ cutoff left right →
  ∣ Cumulant.literalMixedSecondLogDerivative
      (R295.meaning presentation)
      (Cumulant.sourceDirectionOf (R295.meaning presentation) left)
      (Cumulant.sourceDirectionOf (R295.meaning presentation) right)
      cutoff ∣
  ≤ Shell.rootedShell (R295.shellData presentation)
      (R295.scaleOf presentation cutoff)
      (R295.volumeOf presentation cutoff)
      (R295.connectingRoot presentation cutoff left right)
      (R295.physicalDistance presentation left right)
selectedT5AbsoluteLocalization {presentation = presentation}
    {published = published} applicability cutoff left right =
  let
    leftJ = Cumulant.sourceDirectionOf (R295.meaning presentation) left
    rightJ = Cumulant.sourceDirectionOf (R295.meaning presentation) right
    scale = R295.scaleOf presentation cutoff
    volume = R295.volumeOf presentation cutoff

    sourceBound = localized published scale volume leftJ rightJ

    distanceTransported = subst
      (λ distance →
        sourceMagnitude published scale volume leftJ rightJ
        ≤ Shell.rootedShell (R295.shellData presentation)
            scale volume
            (sourceRoot published scale volume leftJ rightJ)
            distance)
      (sourceDistanceIsSelectedPhysicalDistance applicability left right)
      sourceBound

    rootTransported = subst
      (λ root →
        sourceMagnitude published scale volume leftJ rightJ
        ≤ Shell.rootedShell (R295.shellData presentation)
            scale volume root
            (R295.physicalDistance presentation left right))
      (sourceRootIsSelectedConnectingRoot applicability cutoff left right)
      distanceTransported
  in
  subst
    (λ lower → lower ≤ Shell.rootedShell (R295.shellData presentation)
      scale volume
      (R295.connectingRoot presentation cutoff left right)
      (R295.physicalDistance presentation left right))
    (sourceMagnitudeIsSelectedMixedDerivativeAbsolute
      applicability cutoff left right)
    rootTransported

-- Once the applicability weld and the ordinary rational-absolute presentation
-- are supplied, the exact R296 G1 package is compiler output.
toExactT5JMagnitudePresentation :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {presentation : R295.DirectT5StateFamilyJPresentation dataSet extension}
    {published : PublishedTwoJLocalizationForT5 presentation} →
  SelectedT5JApplicability presentation published →
  (∀ value → R278.magnitude extension value ≡ ∣ value ∣) →
  R296.ExactT5JMagnitudePresentation dataSet extension
toExactT5JMagnitudePresentation {presentation = presentation}
    applicability magnitudeIsAbsolute = record
  { R296.ExactT5JMagnitudePresentation.source = presentation
  ; R296.ExactT5JMagnitudePresentation.t5MagnitudeIsRationalAbsolute =
      magnitudeIsAbsolute
  ; R296.ExactT5JMagnitudePresentation.literalTwoJMagnitudeBelowConnectingShell =
      selectedT5AbsoluteLocalization applicability
  }

------------------------------------------------------------------------
-- Boundary / search classification.
------------------------------------------------------------------------

publishedDifferentiatedLocalizationIsNewYMAnalysis : Bool
publishedDifferentiatedLocalizationIsNewYMAnalysis = false

selectedJApplicabilityStillRequired : Bool
selectedJApplicabilityStillRequired = true

shellCarrierMayBeChangedByTypeEqualityAlone : Bool
shellCarrierMayBeChangedByTypeEqualityAlone = false

selectedJApplicabilityCompilerLevel : ProofLevel
selectedJApplicabilityCompilerLevel = machineChecked

publishedDifferentiatedLocalizationLevel : ProofLevel
publishedDifferentiatedLocalizationLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

selectedJApplicabilityPhysicalLevel : ProofLevel
selectedJApplicabilityPhysicalLevel = conditional

publishedDifferentiatedLocalizationIsNewYMAnalysisIsFalse :
  publishedDifferentiatedLocalizationIsNewYMAnalysis ≡ false
publishedDifferentiatedLocalizationIsNewYMAnalysisIsFalse = refl

selectedJApplicabilityStillRequiredIsTrue :
  selectedJApplicabilityStillRequired ≡ true
selectedJApplicabilityStillRequiredIsTrue = refl

shellCarrierMayBeChangedByTypeEqualityAloneIsFalse :
  shellCarrierMayBeChangedByTypeEqualityAlone ≡ false
shellCarrierMayBeChangedByTypeEqualityAloneIsFalse = refl
