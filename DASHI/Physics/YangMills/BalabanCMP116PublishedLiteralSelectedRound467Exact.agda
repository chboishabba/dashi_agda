{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralSelectedRound467Exact where

------------------------------------------------------------------------
-- GOAL-1 Balpha+Bbeta / ROUND467:
-- PUBLISHED CMP116 THEOREM STATED DIRECTLY ON THE LITERAL SELECTED RESPONSE.
--
-- R342 already observed that a post-hoc equality
--
--   abstract source differentiatedMagnitude = literal mixed-J response
--
-- is representation debt.  R463 removed the constructive four-demand radius
-- from the human-proof route but retained that abstract magnitude.
--
-- The least-privilege Clay-facing source theorem is stronger editorially and
-- weaker logically: specialize CMP116 directly to the exact selected
--
--   |D_{J_L} D_{J_R} log Z_{a,L}|
--
-- on one published common analytic domain.  Thus Balpha and Bbeta become ONE
-- source-application theorem rather than two independent physical leaves.
--
-- Bgamma remains independently visible as the physical-time envelope
-- calibration.  The output is again the terminal R387 finite theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact as R387

record PublishedLiteralSelectedLocalization
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
    --------------------------------------------------------------------
    -- Published/common CMP116 source coordinates.
    --------------------------------------------------------------------
    commonDomain :
      Common.CMP116CommonAnalyticRadius
        (R318.Scale base) (R318.Volume base)

    sourceRoot :
      Nat →
      R318.SourceDirection base →
      R318.SourceDirection base →
      R318.Root base

    sourceDistance :
      R318.SourceDirection base →
      R318.SourceDirection base →
      Nat

    sourceEnvelope :
      Nat → R318.Root base → Nat → ℚ

    --------------------------------------------------------------------
    -- Balpha+Bbeta as ONE source application.
    --
    -- The premise is literal membership in the published common domain.
    -- The response on the left is already the selected mixed-log derivative.
    --------------------------------------------------------------------
    literalSelectedCMP116Localization :
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
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative
          (R318.meaning base) leftJ rightJ cutoff)
      ≤
      sourceEnvelope cutoff
        (sourceRoot cutoff leftJ rightJ)
        (sourceDistance leftJ rightJ)

    --------------------------------------------------------------------
    -- Bgamma.
    --------------------------------------------------------------------
    sourceEnvelopeBelowPhysicalClusteringEnvelope :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      sourceEnvelope cutoff
        (sourceRoot cutoff leftJ rightJ)
        (sourceDistance leftJ rightJ)
      ≤
      R281.clusteringEnvelope spectrumSource observable time

open PublishedLiteralSelectedLocalization public

selectedPairInsidePublishedCommonDomain :
  ∀ {Measure TestObservable SpectralObservable Energy
      dataSet extension base tests spectrumSource}
    (source :
      PublishedLiteralSelectedLocalization
        {Measure = Measure} {TestObservable = TestObservable}
        {SpectralObservable = SpectralObservable} {Energy = Energy}
        {dataSet = dataSet} {extension = extension}
        base tests spectrumSource) →
  ∀ cutoff →
  Common.SourceCoordinateInside (commonDomain source)
    (R318.scaleOf base cutoff)
    (R318.volumeOf base cutoff)
selectedPairInsidePublishedCommonDomain {base = base} source cutoff =
  Common.sourceCoordinateInside (commonDomain source)
    (R318.scaleOf base cutoff)
    (R318.volumeOf base cutoff)

selectedResponseBelowSpectrumEnvelope :
  ∀ {Measure TestObservable SpectralObservable Energy
      dataSet extension base tests spectrumSource}
    (source :
      PublishedLiteralSelectedLocalization
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
  R281.clusteringEnvelope spectrumSource observable time
selectedResponseBelowSpectrumEnvelope source cutoff observable time =
  ℚP.≤-trans
    (literalSelectedCMP116Localization source cutoff observable time
      (selectedPairInsidePublishedCommonDomain source cutoff))
    (sourceEnvelopeBelowPhysicalClusteringEnvelope
      source cutoff observable time)

asDirectSelectedSpectralUpper :
  ∀ {Measure TestObservable SpectralObservable Energy
      dataSet extension base tests spectrumSource} →
  PublishedLiteralSelectedLocalization
    {Measure = Measure} {TestObservable = TestObservable}
    {SpectralObservable = SpectralObservable} {Energy = Energy}
    {dataSet = dataSet} {extension = extension}
    base tests spectrumSource →
  R387.DirectSelectedSpectralUpper base tests spectrumSource
asDirectSelectedSpectralUpper source = record
  { R387.DirectSelectedSpectralUpper.selectedResponseBelowSpectrumEnvelope =
      selectedResponseBelowSpectrumEnvelope source
  }

finiteConnectedCovarianceLocalization :
  ∀ {Measure TestObservable SpectralObservable Energy
      dataSet extension base tests spectrumSource}
    (source :
      PublishedLiteralSelectedLocalization
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
  ≤
  R281.clusteringEnvelope spectrumSource observable time
finiteConnectedCovarianceLocalization source =
  R387.finiteSelectedUpper (asDirectSelectedSpectralUpper source)

round467PublishedCommonDomainAuthorityLevel : ProofLevel
round467PublishedCommonDomainAuthorityLevel =
  Common.cmp116CommonAnalyticDomainSourceLevel

round467FiniteCovarianceCompilerLevel : ProofLevel
round467FiniteCovarianceCompilerLevel = machineChecked

-- Exact preferred Goal-1 B source frontier:
--   one literal published CMP116 localization application,
--   one physical source-envelope -> time-envelope calibration.
-- No post-hoc differentiated-magnitude equality is required.
literalRound467PublishedLiteralSelectedLocalizationLevel : ProofLevel
literalRound467PublishedLiteralSelectedLocalizationLevel = conditional
