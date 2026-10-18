{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PublishedSelectedGapProducerExact where

------------------------------------------------------------------------
-- B: PUBLISHED CMP116 DIFFERENTIATED LOCALIZATION -> SELECTED TRANSFER GAP
--
-- No replay of the full source envelope architecture is required.  The source
-- theorem is consumed only on the exact two J-directions selected by R281.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact as R387
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanDirectSelectedUpperToGapFinalExact as Final

record PublishedSelectedCMP116Producer
    {Measure TestObservable SpectralObservable Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests) : Set₁ where
  field
    published :
      Source.PublishedCMP116DifferentiatedLocalization
        (R318.Scale base)
        (R318.Volume base)
        (R318.Root base)
        (R318.SourceDirection base)
        ℚ

    -- exact physical trajectory coordinates
    scaleOfCutoff : Nat → R318.Scale base
    volumeOfCutoff : Nat → R318.Volume base

    selectedPairAdmissible :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      Source.AdmissibleSourcePair published
        (scaleOfCutoff cutoff) (volumeOfCutoff cutoff)
        leftJ rightJ

    -- same-object identification only; no new decay estimate
    sourceResponseIsLiteralSelectedResponse :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      Source.differentiatedMagnitude published
        (scaleOfCutoff cutoff) (volumeOfCutoff cutoff)
        leftJ rightJ
      ≡
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative
          (R318.meaning base) leftJ rightJ cutoff)

    -- calibration of the published source envelope to the selected physical
    -- spectrum; this is where support-distance/time normalization lives.
    publishedEnvelopeBelowSelectedSpectrum :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      Source.sourceEnvelope published
        (scaleOfCutoff cutoff) (volumeOfCutoff cutoff)
        (Source.sourceRoot published
          (scaleOfCutoff cutoff) (volumeOfCutoff cutoff)
          leftJ rightJ)
        (Source.sourceDistance published leftJ rightJ)
      ≤
      R281.clusteringEnvelope spectrumSource observable time

open PublishedSelectedCMP116Producer public

selectedResponseBelowSpectrumEnvelope :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests}
    (producer : PublishedSelectedCMP116Producer base tests spectrumSource)
    cutoff observable time →
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
  in
  R278.magnitude extension
    (Cumulant.literalMixedSecondLogDerivative
      (R318.meaning base) leftJ rightJ cutoff)
  ≤
  R281.clusteringEnvelope spectrumSource observable time
selectedResponseBelowSpectrumEnvelope
    {extension = extension} {base = base} {tests = tests}
    {spectrumSource = spectrumSource}
    producer cutoff observable time =
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
    sourceBound =
      Source.sourceDifferentiatedLocalization
        (published producer)
        (scaleOfCutoff producer cutoff)
        (volumeOfCutoff producer cutoff)
        leftJ rightJ
        (selectedPairAdmissible producer cutoff observable time)
    calibrated =
      ℚP.≤-trans sourceBound
        (publishedEnvelopeBelowSelectedSpectrum
          producer cutoff observable time)
  in
  subst
    (λ lower →
      lower ≤ R281.clusteringEnvelope spectrumSource observable time)
    (sourceResponseIsLiteralSelectedResponse producer cutoff observable time)
    calibrated

asDirectSelectedSpectralUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  PublishedSelectedCMP116Producer base tests spectrumSource →
  R387.DirectSelectedSpectralUpper base tests spectrumSource
asDirectSelectedSpectralUpper producer = record
  { R387.DirectSelectedSpectralUpper.selectedResponseBelowSpectrumEnvelope =
      selectedResponseBelowSpectrumEnvelope producer
  }

publishedSelectedCMP116BuildsPositiveTransferGap :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  PublishedSelectedCMP116Producer base tests spectrumSource →
  R342.SelectedLimitUpperClosure {dataSet = dataSet} →
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum spectrumSource)
    (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource)) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum spectrumSource)
publishedSelectedCMP116BuildsPositiveTransferGap producer closure positive =
  Final.directSelectedUpperBuildsPositiveTransferGapCore
    (asDirectSelectedSpectralUpper producer) closure positive

publishedSelectedCMP116CompilerLevel : ProofLevel
publishedSelectedCMP116CompilerLevel = machineChecked

publishedCMP116LocalizationAuthorityLevel : ProofLevel
publishedCMP116LocalizationAuthorityLevel =
  Source.cmp116DifferentiatedLocalizationAuthorityLevel

selectedCMP116SameObjectApplicationLevel : ProofLevel
selectedCMP116SameObjectApplicationLevel = conditional

selectedCMP116EnvelopeCalibrationLevel : ProofLevel
selectedCMP116EnvelopeCalibrationLevel = conditional
