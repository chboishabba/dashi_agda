{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PublishedAuthoritySelectedT5ApplicationExact where

------------------------------------------------------------------------
-- CMP116 PROOF-BEARING SOURCE AUTHORITY -> SELECTED T5 H1
--
-- Least-privilege application of the source theorem added to
-- `BalabanCMP116DifferentiatedLocalizationSourceExact`.
--
-- Do NOT require a global equality of source/root/distance presentations merely
-- because older adapters happened to store those coordinates separately.  The
-- R320 consumer needs only:
--
--   1. selected J pair lies in the source theorem domain;
--   2. source response magnitude is the selected mixed-log derivative magnitude;
--   3. source exponential envelope is below the selected rooted-shell envelope.
--
-- Those three proof-bearing coordinates are sufficient to compile H1.  Source
-- citation/DOI/QID metadata cannot inhabit any of them.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320

record SelectedT5CMP116AuthorityApplication
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (source : Source.PublishedCMP116DifferentiatedLocalization
      (R318.Scale base)
      (R318.Volume base)
      (R318.Root base)
      (R318.SourceDirection base)
      ℚ)
    : Set₁ where
  field
    -- The imported source authority may package its own order relation.  For the
    -- selected rational T5 consumer we need only this one-way interpretation.
    sourceOrderToRational : ∀ {left right} →
      Source.LessEqual source left right → left ≤ right

    selectedPairAdmissible : ∀ cutoff left right →
      Source.AdmissibleSourcePair source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (Cumulant.sourceDirectionOf (R318.meaning base) left)
        (Cumulant.sourceDirectionOf (R318.meaning base) right)

    sourceMagnitudeIsSelectedMagnitude : ∀ cutoff left right →
      Source.differentiatedMagnitude source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (Cumulant.sourceDirectionOf (R318.meaning base) left)
        (Cumulant.sourceDirectionOf (R318.meaning base) right)
      ≡
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative
          (R318.meaning base)
          (Cumulant.sourceDirectionOf (R318.meaning base) left)
          (Cumulant.sourceDirectionOf (R318.meaning base) right)
          cutoff)

    -- Direct consumer-relative calibration.  Separate source-root and
    -- source-distance equalities are optional stronger producers, not mandatory
    -- once this inequality is paid.
    sourceEnvelopeBelowSelectedRootedShell : ∀ cutoff left right →
      Source.sourceEnvelope source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (Source.sourceRoot source
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          (Cumulant.sourceDirectionOf (R318.meaning base) left)
          (Cumulant.sourceDirectionOf (R318.meaning base) right))
        (Source.sourceDistance source
          (Cumulant.sourceDirectionOf (R318.meaning base) left)
          (Cumulant.sourceDirectionOf (R318.meaning base) right))
      ≤
      Shell.rootedShell (R318.shellData base)
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (R318.connectingRoot base cutoff left right)
        (R318.physicalDistance base left right)

open SelectedT5CMP116AuthorityApplication public

selectedT5LocalizationFromSourceAuthority :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {source : Source.PublishedCMP116DifferentiatedLocalization
      (R318.Scale base)
      (R318.Volume base)
      (R318.Root base)
      (R318.SourceDirection base)
      ℚ} →
  SelectedT5CMP116AuthorityApplication base source →
  ∀ cutoff left right →
  R278.magnitude extension
    (Cumulant.literalMixedSecondLogDerivative
      (R318.meaning base)
      (Cumulant.sourceDirectionOf (R318.meaning base) left)
      (Cumulant.sourceDirectionOf (R318.meaning base) right)
      cutoff)
  ≤
  Shell.rootedShell (R318.shellData base)
    (R318.scaleOf base cutoff)
    (R318.volumeOf base cutoff)
    (R318.connectingRoot base cutoff left right)
    (R318.physicalDistance base left right)
selectedT5LocalizationFromSourceAuthority
    {base = base} {source = source} application cutoff left right =
  let
    scale = R318.scaleOf base cutoff
    volume = R318.volumeOf base cutoff
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right

    sourceBound = sourceOrderToRational application
      (Source.sourceDifferentiatedLocalization source
        scale volume leftJ rightJ
        (selectedPairAdmissible application cutoff left right))

    calibrated = ℚP.≤-trans sourceBound
      (sourceEnvelopeBelowSelectedRootedShell application cutoff left right)
  in
  subst
    (λ lower → lower ≤
      Shell.rootedShell (R318.shellData base)
        scale volume
        (R318.connectingRoot base cutoff left right)
        (R318.physicalDistance base left right))
    (sourceMagnitudeIsSelectedMagnitude application cutoff left right)
    calibrated

sourceAuthorityApplicationBuildsR320Payment :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {source : Source.PublishedCMP116DifferentiatedLocalization
      (R318.Scale base)
      (R318.Volume base)
      (R318.Root base)
      (R318.SourceDirection base)
      ℚ} →
  SelectedT5CMP116AuthorityApplication base source →
  R320.DirectSelectedT5MarkedDecayPayment base
sourceAuthorityApplicationBuildsR320Payment application = record
  { R320.DirectSelectedT5MarkedDecayPayment.mixedDerivativeMagnitudeBelowSelectedShell =
      selectedT5LocalizationFromSourceAuthority application
  }

------------------------------------------------------------------------
-- Status boundary.
------------------------------------------------------------------------

sourceAuthorityStatementLevel : ProofLevel
sourceAuthorityStatementLevel =
  Source.cmp116DifferentiatedLocalizationAuthorityLevel

selectedPairApplicabilityLevel : ProofLevel
selectedPairApplicabilityLevel = conditional

sourceMagnitudeSameObjectLevel : ProofLevel
sourceMagnitudeSameObjectLevel = conditional

sourceEnvelopeCalibrationLevel : ProofLevel
sourceEnvelopeCalibrationLevel = conditional

sourceAuthorityToR320CompilerLevel : ProofLevel
sourceAuthorityToR320CompilerLevel = machineChecked
