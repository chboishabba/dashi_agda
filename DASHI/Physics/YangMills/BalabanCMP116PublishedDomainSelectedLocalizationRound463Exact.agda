{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PublishedDomainSelectedLocalizationRound463Exact where

------------------------------------------------------------------------
-- GOAL-1 Balpha / ROUND463: LEAST-PRIVILEGE PUBLISHED COMMON-DOMAIN ROUTE.
--
-- R104/R114 construct an explicit rational common radius from four normalized
-- demands.  That is a useful constructive fallback, but it is stronger than an
-- ordinary Clay-facing proof needs: CMP116 itself already owns existence of a
-- common analytic domain/radius under its Sect.1 hypotheses.
--
-- This producer therefore starts from:
--   * the published CMP116 differentiated-localization theorem,
--   * one published/common analytic domain object,
--   * one SAME-OBJECT statement that the literal selected CMP119 trajectory
--     lies in that domain.
--
-- Bbeta and Bgamma are then the same response/envelope identifications as R454.
-- The output is the same terminal R387.DirectSelectedSpectralUpper.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact as R387
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341

record PublishedDomainSelectedTwoSourceLocalization
    {Measure TestObservable SpectralObservable Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests)
    : Set₁ where
  field
    commonDomain :
      Common.CMP116CommonAnalyticRadius
        (R318.Scale base) (R318.Volume base)

    source :
      Source.PublishedCMP116DifferentiatedLocalization
        (R318.Scale base)
        (R318.Volume base)
        (R318.Root base)
        (R318.SourceDirection base)
        ℚ

    sourceOrderToRational :
      ∀ {lower upper} →
      Source.LessEqual source lower upper →
      lower ≤ upper

    -- Balpha, least privilege: the source's declared admissible pair predicate
    -- is the physical common-domain predicate on the selected trajectory.
    commonDomainAdmitsSelectedPair :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      Common.SourceCoordinateInside commonDomain
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff) →
      Source.AdmissibleSourcePair source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        leftJ rightJ

    -- Bbeta.
    sourceMagnitudeIsLiteralMixedLogMagnitude :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      Source.differentiatedMagnitude source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        leftJ rightJ
      ≡
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative
          (R318.meaning base) leftJ rightJ cutoff)

    -- Bgamma.
    sourceEnvelopeBelowPhysicalClusteringEnvelope :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      Source.sourceEnvelope source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (Source.sourceRoot source
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          leftJ rightJ)
        (Source.sourceDistance source leftJ rightJ)
      ≤
      R281.clusteringEnvelope spectrumSource observable time

open PublishedDomainSelectedTwoSourceLocalization public

selectedMixedLogBelowSourceEnvelope :
  ∀ {Measure TestObservable SpectralObservable Energy dataSet extension base
      tests spectrumSource}
    (selected :
      PublishedDomainSelectedTwoSourceLocalization
        {Measure = Measure} {TestObservable = TestObservable}
        {SpectralObservable = SpectralObservable} {Energy = Energy}
        {dataSet = dataSet} {extension = extension}
        base tests spectrumSource) →
  ∀ cutoff observable time →
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
  Source.sourceEnvelope (source selected)
    (R318.scaleOf base cutoff)
    (R318.volumeOf base cutoff)
    (Source.sourceRoot (source selected)
      (R318.scaleOf base cutoff)
      (R318.volumeOf base cutoff)
      leftJ rightJ)
    (Source.sourceDistance (source selected) leftJ rightJ)
selectedMixedLogBelowSourceEnvelope
    {base = base} {tests = tests} {spectrumSource = spectrumSource}
    selected cutoff observable time =
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
    inside =
      Common.sourceCoordinateInside (commonDomain selected)
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
    admissible =
      commonDomainAdmitsSelectedPair selected cutoff observable time inside
    publishedBound =
      Source.sourceDifferentiatedLocalization (source selected)
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        leftJ rightJ admissible
    rationalBound = sourceOrderToRational selected publishedBound
  in
  subst
    (λ lower →
      lower ≤
      Source.sourceEnvelope (source selected)
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (Source.sourceRoot (source selected)
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          leftJ rightJ)
        (Source.sourceDistance (source selected) leftJ rightJ))
    (sourceMagnitudeIsLiteralMixedLogMagnitude selected
      cutoff observable time)
    rationalBound

directSelectedSpectralUpper :
  ∀ {Measure TestObservable SpectralObservable Energy dataSet extension base
      tests spectrumSource} →
  PublishedDomainSelectedTwoSourceLocalization
    {Measure = Measure} {TestObservable = TestObservable}
    {SpectralObservable = SpectralObservable} {Energy = Energy}
    {dataSet = dataSet} {extension = extension}
    base tests spectrumSource →
  R387.DirectSelectedSpectralUpper base tests spectrumSource
directSelectedSpectralUpper selected = record
  { R387.DirectSelectedSpectralUpper.selectedResponseBelowSpectrumEnvelope =
      λ cutoff observable time →
        ℚP.≤-trans
          (selectedMixedLogBelowSourceEnvelope selected
            cutoff observable time)
          (sourceEnvelopeBelowPhysicalClusteringEnvelope selected
            cutoff observable time)
  }

finiteConnectedCovarianceLocalization :
  ∀ {Measure TestObservable SpectralObservable Energy dataSet extension base
      tests spectrumSource}
    (selected :
      PublishedDomainSelectedTwoSourceLocalization
        {Measure = Measure} {TestObservable = TestObservable}
        {SpectralObservable = SpectralObservable} {Energy = Energy}
        {dataSet = dataSet} {extension = extension}
        base tests spectrumSource) →
  ∀ cutoff observable time →
  let index = R281.indexFor spectrumSource observable time in
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (R278.left tests index)
    (R278.right tests index)
  ≤ R281.clusteringEnvelope spectrumSource observable time
finiteConnectedCovarianceLocalization selected =
  R387.finiteSelectedUpper (directSelectedSpectralUpper selected)

round463PublishedCommonDomainAuthorityLevel : ProofLevel
round463PublishedCommonDomainAuthorityLevel =
  Common.cmp116CommonAnalyticDomainSourceLevel

round463FiniteSelectedCovarianceCompilerLevel : ProofLevel
round463FiniteSelectedCovarianceCompilerLevel = machineChecked

-- Least-privilege Balpha is now the literal common-domain application above.
-- Four-demand extraction remains a stronger constructive producer, not a
-- mandatory human-proof leaf.
literalRound463PublishedDomainSelectedApplicationLevel : ProofLevel
literalRound463PublishedDomainSelectedApplicationLevel = conditional
