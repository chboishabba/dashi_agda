{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact where

------------------------------------------------------------------------
-- ROUND318 / REMOVE H1 PRODUCER CIRCULARITY
--
-- R295's `DirectT5StateFamilyJPresentation` stores the selected two-J
-- localization theorem itself.  R309 then presents a source-localization
-- authority indexed by that already-localized R295 carrier.  That is useful as
-- a compatibility/transport theorem, but it cannot honestly be the producer of
-- H1 because its input already contains H1.
--
-- This owner separates the carrier from the payment:
--
--   unlocalized selected T5 J carrier
--     + source-localization theorem on the declared source J carrier
--     + same-object/applicability weld
--   ---------------------------------------------------------------
--     localized R295 presentation.
--
-- The source theorem is not re-proved here.  The only physical application
-- leaf on this producer route is the same-object identification of magnitude,
-- connecting root and physical support distance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source

------------------------------------------------------------------------
-- Exact selected finite-T5 source carrier BEFORE the localization theorem.
------------------------------------------------------------------------

record UnlocalizedT5StateFamilyJPresentation
    {Measure TestObservable : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    : Set₁ where
  field
    Scale Volume Root SourceDirection : Set

    calculus : Cumulant.NormalizedLogSourceCalculus
      (R295.t5FiniteExpectationAlgebra dataSet extension)
    meaning : Cumulant.LiteralTwoSourceInsertionMeaning calculus SourceDirection

    shellData : Shell.TraversalShellData Scale Volume Root
    scaleOf : Nat → Scale
    volumeOf : Nat → Volume
    physicalDistance : TestObservable → TestObservable → Nat
    connectingRoot : Nat → TestObservable → TestObservable → Root

    ConnectingClusterMeetsBothSupports :
      Nat → TestObservable → TestObservable → Set

    -- Standard scalar-order fact for the chosen magnitude realization.  This
    -- carries no selected-localization theorem.
    signedBelowMagnitude : ∀ value → value ≤ R278.magnitude extension value

open UnlocalizedT5StateFamilyJPresentation public

------------------------------------------------------------------------
-- Source theorem on the source-native J/root/distance coordinates.
------------------------------------------------------------------------

record PublishedTwoJLocalizationForBase
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : UnlocalizedT5StateFamilyJPresentation dataSet extension)
    : Set₁ where
  field
    sourceMagnitude :
      Scale base → Volume base →
      SourceDirection base → SourceDirection base → ℚ

    sourceRoot :
      Scale base → Volume base →
      SourceDirection base → SourceDirection base → Root base

    sourceDistance : SourceDirection base → SourceDirection base → Nat

    localized : ∀ scale volume left right →
      sourceMagnitude scale volume left right
      ≤ Shell.rootedShell (shellData base)
          scale volume
          (sourceRoot scale volume left right)
          (sourceDistance left right)

open PublishedTwoJLocalizationForBase public

------------------------------------------------------------------------
-- Same-object applicability only.  No inequality is stored here.
------------------------------------------------------------------------

record SelectedBaseJApplicability
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (published : PublishedTwoJLocalizationForBase base)
    : Set₁ where
  field
    sourceMagnitudeIsSelectedMagnitude : ∀ cutoff left right →
      sourceMagnitude published
        (scaleOf base cutoff)
        (volumeOf base cutoff)
        (Cumulant.sourceDirectionOf (meaning base) left)
        (Cumulant.sourceDirectionOf (meaning base) right)
      ≡
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative
          (meaning base)
          (Cumulant.sourceDirectionOf (meaning base) left)
          (Cumulant.sourceDirectionOf (meaning base) right)
          cutoff)

    sourceRootIsSelectedConnectingRoot : ∀ cutoff left right →
      sourceRoot published
        (scaleOf base cutoff)
        (volumeOf base cutoff)
        (Cumulant.sourceDirectionOf (meaning base) left)
        (Cumulant.sourceDirectionOf (meaning base) right)
      ≡ connectingRoot base cutoff left right

    sourceDistanceIsSelectedPhysicalDistance : ∀ left right →
      sourceDistance published
        (Cumulant.sourceDirectionOf (meaning base) left)
        (Cumulant.sourceDirectionOf (meaning base) right)
      ≡ physicalDistance base left right

open SelectedBaseJApplicability public

------------------------------------------------------------------------
-- Compiler: source theorem + applicability manufactures H1.
------------------------------------------------------------------------

selectedMagnitudeLocalizationFromPublished :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {published : PublishedTwoJLocalizationForBase base} →
  SelectedBaseJApplicability base published →
  ∀ cutoff left right →
  R278.magnitude extension
    (Cumulant.literalMixedSecondLogDerivative
      (meaning base)
      (Cumulant.sourceDirectionOf (meaning base) left)
      (Cumulant.sourceDirectionOf (meaning base) right)
      cutoff)
  ≤ Shell.rootedShell (shellData base)
      (scaleOf base cutoff)
      (volumeOf base cutoff)
      (connectingRoot base cutoff left right)
      (physicalDistance base left right)
selectedMagnitudeLocalizationFromPublished
    {base = base} {published = published}
    applicability cutoff left right =
  let
    leftJ = Cumulant.sourceDirectionOf (meaning base) left
    rightJ = Cumulant.sourceDirectionOf (meaning base) right
    scale = scaleOf base cutoff
    volume = volumeOf base cutoff

    sourceBound = localized published scale volume leftJ rightJ

    distanceTransported = subst
      (λ distance →
        sourceMagnitude published scale volume leftJ rightJ
        ≤ Shell.rootedShell (shellData base)
            scale volume
            (sourceRoot published scale volume leftJ rightJ)
            distance)
      (sourceDistanceIsSelectedPhysicalDistance applicability left right)
      sourceBound

    rootTransported = subst
      (λ root →
        sourceMagnitude published scale volume leftJ rightJ
        ≤ Shell.rootedShell (shellData base)
            scale volume root
            (physicalDistance base left right))
      (sourceRootIsSelectedConnectingRoot applicability cutoff left right)
      distanceTransported
  in
  subst
    (λ lower → lower ≤ Shell.rootedShell (shellData base)
      scale volume
      (connectingRoot base cutoff left right)
      (physicalDistance base left right))
    (sourceMagnitudeIsSelectedMagnitude applicability cutoff left right)
    rootTransported

localizeBaseAsR295 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : UnlocalizedT5StateFamilyJPresentation dataSet extension)
    {published : PublishedTwoJLocalizationForBase base} →
  SelectedBaseJApplicability base published →
  R295.DirectT5StateFamilyJPresentation dataSet extension
localizeBaseAsR295 base applicability = record
  { R295.DirectT5StateFamilyJPresentation.Scale = Scale base
  ; R295.DirectT5StateFamilyJPresentation.Volume = Volume base
  ; R295.DirectT5StateFamilyJPresentation.Root = Root base
  ; R295.DirectT5StateFamilyJPresentation.SourceDirection = SourceDirection base
  ; R295.DirectT5StateFamilyJPresentation.calculus = calculus base
  ; R295.DirectT5StateFamilyJPresentation.meaning = meaning base
  ; R295.DirectT5StateFamilyJPresentation.shellData = shellData base
  ; R295.DirectT5StateFamilyJPresentation.scaleOf = scaleOf base
  ; R295.DirectT5StateFamilyJPresentation.volumeOf = volumeOf base
  ; R295.DirectT5StateFamilyJPresentation.physicalDistance = physicalDistance base
  ; R295.DirectT5StateFamilyJPresentation.connectingRoot = connectingRoot base
  ; R295.DirectT5StateFamilyJPresentation.ConnectingClusterMeetsBothSupports =
      ConnectingClusterMeetsBothSupports base
  ; R295.DirectT5StateFamilyJPresentation.signedBelowMagnitude =
      signedBelowMagnitude base
  ; R295.DirectT5StateFamilyJPresentation.differentiatedSourceMagnitudeBoundOnSelectedDirections =
      selectedMagnitudeLocalizationFromPublished applicability
  }

------------------------------------------------------------------------
-- Boundary / proof-search classification.
------------------------------------------------------------------------

record Round318Boundary : Set where
  constructor round318-boundary
  field
    producerInputAlreadyContainsH1 : Bool
    producerInputAlreadyContainsH1IsFalse :
      producerInputAlreadyContainsH1 ≡ false

    sourceLocalizationAlonePaysSelectedH1 : Bool
    sourceLocalizationAlonePaysSelectedH1IsFalse :
      sourceLocalizationAlonePaysSelectedH1 ≡ false

    sourceLocalizationPlusApplicabilityPaysSelectedH1 : Bool
    sourceLocalizationPlusApplicabilityPaysSelectedH1IsTrue :
      sourceLocalizationPlusApplicabilityPaysSelectedH1 ≡ true

    selectedJApplicabilityStillPhysical : Bool
    selectedJApplicabilityStillPhysicalIsTrue :
      selectedJApplicabilityStillPhysical ≡ true

    publishedLocalizationIsNewYMAnalysis : Bool
    publishedLocalizationIsNewYMAnalysisIsFalse :
      publishedLocalizationIsNewYMAnalysis ≡ false

    sourceRouteMandatoryForCanonicalB : Bool
    sourceRouteMandatoryForCanonicalBIsFalse :
      sourceRouteMandatoryForCanonicalB ≡ false

canonicalRound318Boundary : Round318Boundary
canonicalRound318Boundary =
  round318-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl

round318LocalizationCompilerLevel : ProofLevel
round318LocalizationCompilerLevel = machineChecked

round318PublishedLocalizationLevel : ProofLevel
round318PublishedLocalizationLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

round318SelectedJApplicabilityLevel : ProofLevel
round318SelectedJApplicabilityLevel = conditional
