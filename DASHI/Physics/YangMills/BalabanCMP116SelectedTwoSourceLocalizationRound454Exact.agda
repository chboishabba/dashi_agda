{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedTwoSourceLocalizationRound454Exact where

------------------------------------------------------------------------
-- GOAL-1 B / ROUND454
-- REFEREE-FACING CMP116 SELECTED TWO-SOURCE LOCALIZATION LEMMA
--
-- Primary source:
-- T. Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", CMP 116 (1988), 1--22.
--
-- Goal-1 proof architecture:
--
--   Bα  the literal selected two-J pair lies in the common CMP116 analytic
--       domain, uniformly along the finite trajectory;
--   Bβ  the published differentiated quantity is the literal mixed-log
--       response (hence the exact finite connected covariance);
--   Bγ  the published source envelope is bounded by the physical selected
--       clustering envelope, using only one-sided physical geometry/rate.
--
-- CMP116 (1.23)--(1.36) is used as a published localization theorem.
-- We do NOT reconstruct its internal (1.26)--(1.29) cluster counting here.
-- R444--R453 remain optional provenance/decompression for applicability.
--
-- The conclusion is precisely R387.DirectSelectedSpectralUpper, the terminal
-- finite B theorem consumed by the existing continuum/OS/spectral compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _<_)
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
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116R281SelectedSourceUpperRound343Exact as R343
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact as R387

record SelectedTwoSourceLocalization
    {Measure TestObservable SpectralObservable Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    (source : R338.CanonicalCommonDomainCMP116Source base demands)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests)
    : Set₁ where
  field
    --------------------------------------------------------------------
    -- Bβ: SAME OBJECT.
    --
    -- This is the only equality needed between Bałaban's source theorem and
    -- the literal selected two-source response.  R341 then identifies the
    -- latter with the exact finite connected covariance.
    --------------------------------------------------------------------
    sourceMagnitudeIsLiteralMixedLogMagnitude :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      R338.differentiatedMagnitude source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        leftJ rightJ
      ≡
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative
          (R318.meaning base) leftJ rightJ cutoff)

    --------------------------------------------------------------------
    -- Bγ: PHYSICAL ENVELOPE CALIBRATION.
    --
    -- This is intentionally one-sided.  The proof may use the shared Hessian
    -- shell, R391/R392 one-sided distance geometry, or an equivalent direct
    -- specialization of the published exponential envelope.  Equality of
    -- source, physical and Euclidean distances is not required.
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
      R338.sourceEnvelope source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (R338.sourceRoot source
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          leftJ rightJ)
        (R338.sourceDistance source leftJ rightJ)
      ≤
      R281.clusteringEnvelope spectrumSource observable time

open SelectedTwoSourceLocalization public

------------------------------------------------------------------------
-- Bα: applicability is compiler-owned once the finite normalized CMP116
-- demands are extracted on the actual trajectory.
------------------------------------------------------------------------

commonAnalyticRadiusPositive :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests}
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    (source : R338.CanonicalCommonDomainCMP116Source base demands)
    (selected : SelectedTwoSourceLocalization
      base demands source tests spectrumSource) →
  0ℚ < R104.canonicalCommonRadius demands
commonAnalyticRadiusPositive demands source selected =
  R104.canonicalCommonRadiusPositive demands

selectedPairAdmissible :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests}
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    (source : R338.CanonicalCommonDomainCMP116Source base demands)
    (selected : SelectedTwoSourceLocalization
      base demands source tests spectrumSource) →
  ∀ cutoff observable time →
  Common.SourceCoordinateInside
    (R114.canonicalCMP116CommonDomain
      {R318.Scale base} {R318.Volume base} demands)
    (R318.scaleOf base cutoff)
    (R318.volumeOf base cutoff)
selectedPairAdmissible demands source selected cutoff observable time =
  Common.sourceCoordinateInside
    (R114.canonicalCMP116CommonDomain
      {R318.Scale _} {R318.Volume _} demands)
    (R318.scaleOf _ cutoff)
    (R318.volumeOf _ cutoff)

------------------------------------------------------------------------
-- Published CMP116 theorem specialized to the literal selected pair.
------------------------------------------------------------------------

selectedMixedLogBelowSourceEnvelope :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  (selected : SelectedTwoSourceLocalization
    base demands source tests spectrumSource) →
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
  R338.sourceEnvelope source
    (R318.scaleOf base cutoff)
    (R318.volumeOf base cutoff)
    (R338.sourceRoot source
      (R318.scaleOf base cutoff)
      (R318.volumeOf base cutoff)
      leftJ rightJ)
    (R338.sourceDistance source leftJ rightJ)
selectedMixedLogBelowSourceEnvelope
    {base = base} {demands = demands} {source = source}
    {tests = tests} {spectrumSource = spectrumSource}
    selected cutoff observable time =
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right

    sourceBound =
      R338.differentiatedLocalizationOnCanonicalCommonDomain source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        leftJ rightJ
        (Common.sourceCoordinateInside
          (R114.canonicalCMP116CommonDomain
            {R318.Scale base} {R318.Volume base} demands)
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff))
  in
  subst
    (λ lower →
      lower ≤
      R338.sourceEnvelope source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (R338.sourceRoot source
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          leftJ rightJ)
        (R338.sourceDistance source leftJ rightJ))
    (sourceMagnitudeIsLiteralMixedLogMagnitude selected
      cutoff observable time)
    sourceBound

asR343 :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  SelectedTwoSourceLocalization base demands source tests spectrumSource →
  R342.SelectedLimitUpperClosure {dataSet = dataSet} →
  R343.SelectedResponseSourceUpperApplication
    base demands source tests spectrumSource
asR343 selected limitClosure = record
  { R343.SelectedResponseSourceUpperApplication.selectedResponseBelowSourceEnvelope =
      selectedMixedLogBelowSourceEnvelope selected
  ; R343.SelectedResponseSourceUpperApplication.sourceEnvelopeBelowSpectrumEnvelope =
      sourceEnvelopeBelowPhysicalClusteringEnvelope selected
  ; R343.SelectedResponseSourceUpperApplication.rationalUpperClosedUnderSelectedLimit =
      limitClosure
  }

------------------------------------------------------------------------
-- Main referee-facing finite theorem.
------------------------------------------------------------------------

directSelectedSpectralUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  SelectedTwoSourceLocalization base demands source tests spectrumSource →
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
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  (selected : SelectedTwoSourceLocalization
    base demands source tests spectrumSource) →
  ∀ cutoff observable time →
  let index = R281.indexFor spectrumSource observable time in
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (R278.left tests index)
    (R278.right tests index)
  ≤
  R281.clusteringEnvelope spectrumSource observable time
finiteConnectedCovarianceLocalization selected =
  R387.finiteSelectedUpper (directSelectedSpectralUpper selected)

------------------------------------------------------------------------
-- Goal-1 status.
------------------------------------------------------------------------

round454PublishedCMP116LocalizationReusedNotReprovedLevel : ProofLevel
round454PublishedCMP116LocalizationReusedNotReprovedLevel =
  R338.round338CanonicalSourceStatementAuthorityLevel

round454CommonDomainRadiusCompilerLevel : ProofLevel
round454CommonDomainRadiusCompilerLevel =
  R114.cmp116FiniteDemandsToCommonRadiusObjectLevel

round454SelectedFiniteCovarianceCompilerLevel : ProofLevel
round454SelectedFiniteCovarianceCompilerLevel = machineChecked

-- Genuine Goal-1 B source/application payments:
--   Bα extract/identify the finite normalized common-domain demands on the
--      literal cutoff trajectory;
--   Bβ identify the published differentiated magnitude with the literal
--      selected mixed-log response;
--   Bγ prove the published envelope is bounded by the selected physical
--      clustering envelope using uniform constants and one-sided geometry.
literalRound454SelectedTwoSourceLocalizationLevel : ProofLevel
literalRound454SelectedTwoSourceLocalizationLevel = conditional
