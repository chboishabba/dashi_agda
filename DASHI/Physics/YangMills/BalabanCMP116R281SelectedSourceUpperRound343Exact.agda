{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R281SelectedSourceUpperRound343Exact where

------------------------------------------------------------------------
-- ROUND343 / PARETO-WEAKEN R341 B1 TO THE ACTUAL MASS-GAP CONSUMER
--
-- R341 asks for
--
--   sourceMagnitude = selected literal mixed-log magnitude
--
-- and then uses the published CMP116 source theorem
--
--   sourceMagnitude <= sourceEnvelope
--
-- only to conclude
--
--   selected literal mixed-log magnitude <= sourceEnvelope.
--
-- The equality is therefore stronger than this terminal consumer requires.
-- The least-privilege selected-source application is the one-sided theorem
-- above on the exact selected pair.  Together with the independent
-- sourceEnvelope <= R281 spectral-envelope calibration and standard one-sided
-- closure under the actual R278 convergence, it yields the same subgap upper.
--
-- The old R341 application mechanically compiles to this weaker surface.  The
-- converse is intentionally unavailable: an upper bound does not recover the
-- source-response equality.  No fresh YM decay estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341

record SelectedResponseSourceUpperApplication
    {Measure TestObservable SpectralObservable Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    (source : R338.CanonicalCommonDomainCMP116Source base demands)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests)
    : Set₁ where
  field
    -- Least-privilege physical/source application: apply the published CMP116
    -- differentiated-localization theorem directly to the selected J pair.
    selectedResponseBelowSourceEnvelope :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
          leftJ rightJ cutoff)
      ≤
      R338.sourceEnvelope source
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
        (R338.sourceRoot source
          (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
          leftJ rightJ)
        (R338.sourceDistance source leftJ rightJ)

    -- Independent quantitative calibration retained from R341.
    sourceEnvelopeBelowSpectrumEnvelope :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      R338.sourceEnvelope source
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
        (R338.sourceRoot source
          (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
          leftJ rightJ)
        (R338.sourceDistance source leftJ rightJ)
      ≤
      R281.clusteringEnvelope spectrumSource observable time

    -- Shared ordered-limit closure; not a YM-specific estimate.
    rationalUpperClosedUnderSelectedLimit :
      (sequence : Nat → ℚ) (target upper : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open SelectedResponseSourceUpperApplication public

------------------------------------------------------------------------
-- Old R341 application -> weaker R343 application.
------------------------------------------------------------------------

r341ApplicationBuildsR343 :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests} →
  R341.CanonicalCMP116R281ModeSelectedApplication
    base demands source tests spectrumSource →
  SelectedResponseSourceUpperApplication
    base demands source tests spectrumSource
r341ApplicationBuildsR343
    {base = base} {demands = demands} {source = source}
    {tests = tests} {spectrumSource = spectrumSource} application = record
  { selectedResponseBelowSourceEnvelope = λ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
        commonInside =
          Common.sourceCoordinateInside
            (R114.canonicalCMP116CommonDomain
              {R318.Scale base} {R318.Volume base} demands)
            (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
        sourceBound =
          R338.differentiatedLocalizationOnCanonicalCommonDomain source
            (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
            leftJ rightJ commonInside
        sourceToSelected =
          R341.sourceMagnitudeIsSelectedMixedLogMagnitude application
            cutoff observable time
      in
      subst
        (λ lower → lower ≤
          R338.sourceEnvelope source
            (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
            (R338.sourceRoot source
              (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
              leftJ rightJ)
            (R338.sourceDistance source leftJ rightJ))
        sourceToSelected
        sourceBound
  ; sourceEnvelopeBelowSpectrumEnvelope =
      R341.sourceEnvelopeBelowSpectrumEnvelope application
  ; rationalUpperClosedUnderSelectedLimit =
      R341.rationalUpperClosedUnderSelectedLimit application
  }

------------------------------------------------------------------------
-- Direct finite upper on the selected covariance sequence.
------------------------------------------------------------------------

finiteSelectedUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests} →
  (application : SelectedResponseSourceUpperApplication
    base demands source tests spectrumSource) →
  ∀ cutoff observable time →
  let
    index = R281.indexFor spectrumSource observable time
  in
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (R278.left tests index) (R278.right tests index)
  ≤ R281.clusteringEnvelope spectrumSource observable time
finiteSelectedUpper
    {extension = extension} {base = base} {source = source}
    {tests = tests} {spectrumSource = spectrumSource}
    application cutoff observable time =
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
    selectedBound =
      selectedResponseBelowSourceEnvelope application cutoff observable time
    selectedToCovariance =
      R341.mixedLogMagnitudeIsFiniteSelectedCovarianceMagnitude
        base cutoff left right
    covarianceToSourceEnvelope =
      subst
        (λ lower → lower ≤
          R338.sourceEnvelope source
            (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
            (R338.sourceRoot source
              (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
              leftJ rightJ)
            (R338.sourceDistance source leftJ rightJ))
        selectedToCovariance
        selectedBound
    envelopeToSpectrum =
      sourceEnvelopeBelowSpectrumEnvelope application cutoff observable time
  in
  ℚP.≤-trans covarianceToSourceEnvelope envelopeToSpectrum

------------------------------------------------------------------------
-- Same reconstructed subgap upper as R341, without primitive B1 equality.
------------------------------------------------------------------------

selectedSourceUpperBuildsSubgapUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests} →
  SelectedResponseSourceUpperApplication
    base demands source tests spectrumSource →
  Gap.SubgapModeClusteringUpper
    (R281.asReconstructedClusteringSpectrum spectrumSource)
selectedSourceUpperBuildsSubgapUpper
    {dataSet = dataSet} {extension = extension}
    {base = base} {tests = tests} {spectrumSource = spectrumSource}
    application energy mode time =
  let
    observable = R281.modeObservable spectrumSource energy mode
    index = R281.indexFor spectrumSource observable time
    sequence = λ cutoff →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        (R278.left tests index) (R278.right tests index)
    target =
      R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        (R278.left tests index) (R278.right tests index)
    upper = R281.clusteringEnvelope spectrumSource observable time
  in
  rationalUpperClosedUnderSelectedLimit application
    sequence target upper
    (R278.selectedConnectedCovarianceMagnitudeConverges
      extension tests index)
    (λ cutoff → finiteSelectedUpper application cutoff observable time)

------------------------------------------------------------------------
-- Pareto boundary.
------------------------------------------------------------------------

sourceMagnitudeEqualityPrimitiveForMassGapConsumer : Bool
sourceMagnitudeEqualityPrimitiveForMassGapConsumer = false

selectedResponseSourceUpperStillRequired : Bool
selectedResponseSourceUpperStillRequired = true

sourceEnvelopeCalibrationStillRequired : Bool
sourceEnvelopeCalibrationStillRequired = true

oldR341ApplicationCompilesToR343 : Bool
oldR341ApplicationCompilesToR343 = true

-- The weaker one-sided application intentionally does not recover source = selected.
r343DoesNotRecoverSourceMagnitudeEquality : Bool
r343DoesNotRecoverSourceMagnitudeEquality = true

freshYMDecayEstimateIntroduced : Bool
freshYMDecayEstimateIntroduced = false

clayPromotion : Bool
clayPromotion = false

round343CompilerLevel : ProofLevel
round343CompilerLevel = machineChecked

round343SelectedResponseSourceUpperLevel : ProofLevel
round343SelectedResponseSourceUpperLevel = conditional

round343EnvelopeCalibrationLevel : ProofLevel
round343EnvelopeCalibrationLevel = R341.round341EnvelopeCalibrationLevel

round343OneSidedOrderClosureLevel : ProofLevel
round343OneSidedOrderClosureLevel = R341.round341OneSidedOrderClosureLevel
