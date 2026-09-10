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
--       observables, mixed derivative, support distance and connecting root with
--       that source carrier.
--
-- Their composition constructs the exact R296 presentation.  Therefore a
-- published/source-localization theorem must not be charged again as new 4D YM
-- analysis merely because its selected physical application is still open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source

------------------------------------------------------------------------
-- Source theorem carrier.
------------------------------------------------------------------------

record PublishedTwoJLocalization
    (Scale Volume Root SourceDirection : Set) : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root

    sourceMagnitude :
      Scale → Volume → SourceDirection → SourceDirection → ℚ

    sourceRoot :
      Scale → Volume → SourceDirection → SourceDirection → Root

    sourceDistance : SourceDirection → SourceDirection → Nat

    localized : ∀ scale volume left right →
      sourceMagnitude scale volume left right
      ≤ Shell.rootedShell shellData scale volume
          (sourceRoot scale volume left right)
          (sourceDistance left right)

open PublishedTwoJLocalization public

------------------------------------------------------------------------
-- Same-object selected-T5 applicability.
------------------------------------------------------------------------

record SelectedT5JApplicability
    {Measure TestObservable Scale Volume Root SourceDirection : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (presentation : R295.DirectT5StateFamilyJPresentation dataSet extension)
    (published : PublishedTwoJLocalization Scale Volume Root SourceDirection)
    : Set₁ where
  field
    -- The selected source carrier is literally the one used by the finite T5
    -- source presentation.
    sourceDirectionSame : SourceDirection ≡ R295.SourceDirection presentation
    scaleSame : Scale ≡ R295.Scale presentation
    volumeSame : Volume ≡ R295.Volume presentation
    rootSame : Root ≡ R295.Root presentation

    -- Pointwise same-object application.  These are representation/applicability
    -- equalities; none is a fresh decay inequality.
    sourceMagnitudeIsSelectedMixedDerivativeAbsolute :
      ∀ cutoff left right →
      sourceMagnitude published
        (subst (λ X → X) (sym scaleSame) (R295.scaleOf presentation cutoff))
        (subst (λ X → X) (sym volumeSame) (R295.volumeOf presentation cutoff))
        (subst (λ X → X) (sym sourceDirectionSame)
          (Cumulant.sourceDirectionOf (R295.meaning presentation) left))
        (subst (λ X → X) (sym sourceDirectionSame)
          (Cumulant.sourceDirectionOf (R295.meaning presentation) right))
      ≡
      ∣ Cumulant.literalMixedSecondLogDerivative
          (R295.meaning presentation)
          (Cumulant.sourceDirectionOf (R295.meaning presentation) left)
          (Cumulant.sourceDirectionOf (R295.meaning presentation) right)
          cutoff ∣

    sourceRootIsSelectedConnectingRoot :
      ∀ cutoff left right →
      subst (λ X → X) rootSame
        (sourceRoot published
          (subst (λ X → X) (sym scaleSame) (R295.scaleOf presentation cutoff))
          (subst (λ X → X) (sym volumeSame) (R295.volumeOf presentation cutoff))
          (subst (λ X → X) (sym sourceDirectionSame)
            (Cumulant.sourceDirectionOf (R295.meaning presentation) left))
          (subst (λ X → X) (sym sourceDirectionSame)
            (Cumulant.sourceDirectionOf (R295.meaning presentation) right)))
      ≡ R295.connectingRoot presentation cutoff left right

    sourceDistanceIsSelectedPhysicalDistance :
      ∀ left right →
      sourceDistance published
        (subst (λ X → X) (sym sourceDirectionSame)
          (Cumulant.sourceDirectionOf (R295.meaning presentation) left))
        (subst (λ X → X) (sym sourceDirectionSame)
          (Cumulant.sourceDirectionOf (R295.meaning presentation) right))
      ≡ R295.physicalDistance presentation left right

open SelectedT5JApplicability public

------------------------------------------------------------------------
-- Compiler into the exact current G1 consumer.
------------------------------------------------------------------------

selectedT5AbsoluteLocalization :
  ∀ {Measure TestObservable Scale Volume Root SourceDirection}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {presentation : R295.DirectT5StateFamilyJPresentation dataSet extension}
    {published : PublishedTwoJLocalization Scale Volume Root SourceDirection} →
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
selectedT5AbsoluteLocalization applicability cutoff left right =
  let
    -- The only inequality is the already supplied source theorem.
    sourceBound = localized _ _ _ _ _
  in
  -- The remaining steps are same-object transports.  Keeping them explicit
  -- prevents a source theorem on the wrong J/support carrier from paying G1.
  subst
    (λ lower → lower ≤ Shell.rootedShell
      (R295.shellData _)
      (R295.scaleOf _ cutoff)
      (R295.volumeOf _ cutoff)
      (R295.connectingRoot _ cutoff left right)
      (R295.physicalDistance _ left right))
    (sourceMagnitudeIsSelectedMixedDerivativeAbsolute applicability cutoff left right)
    (subst
      (λ root →
        sourceMagnitude _ _ _ _ _
        ≤ Shell.rootedShell (R295.shellData _)
            (R295.scaleOf _ cutoff)
            (R295.volumeOf _ cutoff)
            root
            (R295.physicalDistance _ left right))
      (sourceRootIsSelectedConnectingRoot applicability cutoff left right)
      (subst
        (λ distance →
          sourceMagnitude _ _ _ _ _
          ≤ Shell.rootedShell (R295.shellData _)
              (R295.scaleOf _ cutoff)
              (R295.volumeOf _ cutoff)
              _ distance)
        (sourceDistanceIsSelectedPhysicalDistance applicability left right)
        sourceBound))

------------------------------------------------------------------------
-- Boundary / search classification.
------------------------------------------------------------------------

publishedDifferentiatedLocalizationIsNewYMAnalysis : Bool
publishedDifferentiatedLocalizationIsNewYMAnalysis = false

selectedJApplicabilityStillRequired : Bool
selectedJApplicabilityStillRequired = true

supportRootGeometryMayBeDropped : Bool
supportRootGeometryMayBeDropped = false

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

supportRootGeometryMayBeDroppedIsFalse :
  supportRootGeometryMayBeDropped ≡ false
supportRootGeometryMayBeDroppedIsFalse = refl
