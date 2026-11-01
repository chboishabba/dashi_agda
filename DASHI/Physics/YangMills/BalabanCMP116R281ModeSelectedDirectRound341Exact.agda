{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact where

------------------------------------------------------------------------
-- ROUND341 / CMP116 -> R281 MODE-SELECTED UPPER WITHOUT CONVERGENCE REPACKAGING
--
-- R281 constructs the reconstructed spectrum directly on R278's continuum
-- covariance carrier.  Therefore a source-native CMP116 producer does not need
-- an additional "same-spectrum convergence" theorem when its finite response
-- is identified with the selected mixed log derivative:
--
--   CMP116 source magnitude
--     = literal mixed-log magnitude                 [same-object weld]
--     = finite selected covariance magnitude        [generic cumulant compiler]
--     -> continuum covariance magnitude             [R278 convergence]
--     = reconstructed spectral correlation          [R281, refl].
--
-- The mode/time -> source directions are also compiler output: R281 selects the
-- covariance index, R278 selects its left/right test observables, and the base
-- source meaning maps those observables to J-directions.
--
-- The only source/application information left here is:
--   1. source-response same-object identity;
--   2. source-envelope -> spectral-envelope comparison;
-- plus one-sided closedness of the actual R278 convergence relation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

------------------------------------------------------------------------
-- Generic finite identity on the UNLOCALIZED selected T5 carrier.
------------------------------------------------------------------------

mixedLogMagnitudeIsFiniteSelectedCovarianceMagnitude :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    cutoff left right →
  R278.magnitude extension
    (Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
      (Cumulant.sourceDirectionOf (R318.meaning base) left)
      (Cumulant.sourceDirectionOf (R318.meaning base) right)
      cutoff)
  ≡
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff) left right
mixedLogMagnitudeIsFiniteSelectedCovarianceMagnitude
    {dataSet = dataSet} {extension = extension} base cutoff left right =
  trans
    (cong (R278.magnitude extension)
      (cong (λ response → response cutoff)
        (Cumulant.literalMixedLogDerivativeIsConnectedCovariance
          (R318.meaning base) left right)))
    (cong (R278.magnitude extension)
      (R295.sourceConnectedCovarianceIsExactFiniteT5
        dataSet extension left right cutoff))

record CanonicalCMP116R281ModeSelectedApplication
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
    -- Same-object payment only: source E^(2)/Pi response magnitude really is
    -- the literal selected mixed-log derivative magnitude on the directions
    -- generated from the selected covariance pair.
    sourceMagnitudeIsSelectedMixedLogMagnitude :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      R338.differentiatedMagnitude source
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
        leftJ rightJ
      ≡
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
          leftJ rightJ cutoff)

    -- Quantitative calibration only.  Keep the source prefactor/rate native;
    -- do not force it through the configured coefficient-one rooted shell.
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

    -- Shared analysis/topology authority, not a new YM estimate.
    rationalUpperClosedUnderSelectedLimit :
      (sequence : Nat → ℚ) (target upper : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open CanonicalCMP116R281ModeSelectedApplication public

finiteSelectedSourceUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests} →
  (application : CanonicalCMP116R281ModeSelectedApplication
    base demands source tests spectrumSource) →
  ∀ cutoff observable time →
  let
    index = R281.indexFor spectrumSource observable time
  in
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (R278.left tests index) (R278.right tests index)
  ≤ R281.clusteringEnvelope spectrumSource observable time
finiteSelectedSourceUpper
    {dataSet = dataSet} {extension = extension} {base = base}
    {demands = demands} {source = source} {tests = tests}
    {spectrumSource = spectrumSource}
    application cutoff observable time =
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
      sourceMagnitudeIsSelectedMixedLogMagnitude application
        cutoff observable time
    selectedToCovariance =
      mixedLogMagnitudeIsFiniteSelectedCovarianceMagnitude
        base cutoff left right
    sourceToCovariance = trans sourceToSelected selectedToCovariance
    sourceEnvelopeToSpectrum =
      sourceEnvelopeBelowSpectrumEnvelope application cutoff observable time
  in
  ℚP.≤-trans
    (subst
      (λ lower →
        lower ≤ R338.sourceEnvelope source
          (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
          (R338.sourceRoot source
            (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
            leftJ rightJ)
          (R338.sourceDistance source leftJ rightJ))
      sourceToCovariance
      sourceBound)
    sourceEnvelopeToSpectrum

canonicalCMP116R281BuildsSubgapUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests} →
  CanonicalCMP116R281ModeSelectedApplication
    base demands source tests spectrumSource →
  Gap.SubgapModeClusteringUpper (R281.asReconstructedClusteringSpectrum spectrumSource)
canonicalCMP116R281BuildsSubgapUpper
    {dataSet = dataSet} {extension = extension} {base = base}
    {tests = tests} {spectrumSource = spectrumSource} application
    energy mode time =
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
    targetUpper =
      rationalUpperClosedUnderSelectedLimit application
        sequence target upper
        (R278.selectedConnectedCovarianceMagnitudeConverges
          extension tests index)
        (λ cutoff → finiteSelectedSourceUpper application cutoff observable time)
  in
  targetUpper

record Round341Boundary : Set where
  constructor round341-boundary
  field
    independentModeToSourceDirectionLeaf : Bool
    independentModeToSourceDirectionLeafIsFalse :
      independentModeToSourceDirectionLeaf ≡ false

    independentSameSpectrumConvergenceLeaf : Bool
    independentSameSpectrumConvergenceLeafIsFalse :
      independentSameSpectrumConvergenceLeaf ≡ false

    continuumCovarianceSpectrumWeldLeaf : Bool
    continuumCovarianceSpectrumWeldLeafIsFalse :
      continuumCovarianceSpectrumWeldLeaf ≡ false

    sourceResponseSameObjectStillRequired : Bool
    sourceResponseSameObjectStillRequiredIsTrue :
      sourceResponseSameObjectStillRequired ≡ true

    sourceEnvelopeCalibrationStillRequired : Bool
    sourceEnvelopeCalibrationStillRequiredIsTrue :
      sourceEnvelopeCalibrationStillRequired ≡ true

    oneSidedOrderClosureStillRequired : Bool
    oneSidedOrderClosureStillRequiredIsTrue :
      oneSidedOrderClosureStillRequired ≡ true

    freshYMDecayEstimateIntroduced : Bool
    freshYMDecayEstimateIntroducedIsFalse :
      freshYMDecayEstimateIntroduced ≡ false

canonicalRound341Boundary : Round341Boundary
canonicalRound341Boundary =
  round341-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl

round341CompilerLevel : ProofLevel
round341CompilerLevel = machineChecked

round341SourceResponseSameObjectLevel : ProofLevel
round341SourceResponseSameObjectLevel = conditional

round341EnvelopeCalibrationLevel : ProofLevel
round341EnvelopeCalibrationLevel = conditional

round341OneSidedOrderClosureLevel : ProofLevel
round341OneSidedOrderClosureLevel = standardImported

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
