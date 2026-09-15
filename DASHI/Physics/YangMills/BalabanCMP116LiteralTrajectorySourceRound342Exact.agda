{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact where

------------------------------------------------------------------------
-- ROUND342 / LITERAL SELECTED-TRAJECTORY CMP116 SOURCE
--
-- R341 still carried a post-hoc same-object equality between an abstract
-- source `differentiatedMagnitude` and the literal selected T5 mixed-log
-- derivative magnitude.  That equality is representation debt: the direct
-- source payment needed by the canonical B consumer can instead be stated on
-- the literal selected trajectory from the start.
--
-- This owner therefore keeps the genuine theorem-bearing coordinates only:
--
--   1. CMP116 differentiated localization, now stated directly on the literal
--      mixed-log response and still guarded by the canonical common U,J domain;
--   2. quantitative comparison of the source-native envelope with the exact
--      reconstructed-spectrum clustering envelope;
--   3. standard one-sided closedness of the selected rational limit.
--
-- The mixed-log response -> finite connected covariance identity is compiler
-- output from the existing cumulant/T5 algebra.  No citation, ProofLevel label,
-- or source name manufactures the literal localization inhabitant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
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
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341

------------------------------------------------------------------------
-- Literal selected-trajectory source ABI.
------------------------------------------------------------------------

record LiteralTrajectoryCMP116Source
    {Measure TestObservable SpectralObservable Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests)
    : Set₁ where
  field
    sourceRoot :
      Nat → R318.SourceDirection base → R318.SourceDirection base → R318.Root base

    sourceDistance :
      R318.SourceDirection base → R318.SourceDirection base → Nat

    sourceEnvelope : Nat → R318.Root base → Nat → ℚ

    SourceEnvelopeHasPositiveExponentialTreeDecay : Set
    sourceEnvelopeHasPositiveExponentialTreeDecay :
      SourceEnvelopeHasPositiveExponentialTreeDecay

    -- The actual source/application payment.  The response on the left is the
    -- literal selected mixed-log response; there is no independently named
    -- source magnitude and therefore no later same-object equality to prove.
    literalDifferentiatedLocalization :
      ∀ cutoff leftJ rightJ →
      Common.SourceCoordinateInside
        (R114.canonicalCMP116CommonDomain
          {R318.Scale base} {R318.Volume base} demands)
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff) →
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
          leftJ rightJ cutoff)
      ≤
      sourceEnvelope cutoff
        (sourceRoot cutoff leftJ rightJ)
        (sourceDistance leftJ rightJ)

    -- Quantitative calibration remains theorem-bearing.  We do not identify a
    -- source-native exponential prefactor/rate with the spectral envelope by
    -- naming convention.
    sourceEnvelopeBelowSpectrumEnvelope :
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
      ≤ R281.clusteringEnvelope spectrumSource observable time

    -- Standard ordered-limit authority on the concrete rational carrier.
    rationalUpperClosedUnderSelectedLimit :
      (sequence : Nat → ℚ) (target upper : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open LiteralTrajectoryCMP116Source public

------------------------------------------------------------------------
-- Finite selected upper: literal source theorem -> exact T5 covariance.
------------------------------------------------------------------------

finiteSelectedLiteralUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  (source : LiteralTrajectoryCMP116Source
    base demands tests spectrumSource) →
  ∀ cutoff observable time →
  let
    index = R281.indexFor spectrumSource observable time
  in
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (R278.left tests index) (R278.right tests index)
  ≤ R281.clusteringEnvelope spectrumSource observable time
finiteSelectedLiteralUpper
    {dataSet = dataSet} {extension = extension} {base = base}
    {demands = demands} {tests = tests} {spectrumSource = spectrumSource}
    source cutoff observable time =
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
    literalBound =
      literalDifferentiatedLocalization source cutoff leftJ rightJ commonInside
    literalToCovariance =
      R341.mixedLogMagnitudeIsFiniteSelectedCovarianceMagnitude
        base cutoff left right
    covarianceToSourceEnvelope =
      subst
        (λ lower →
          lower ≤ sourceEnvelope source cutoff
            (sourceRoot source cutoff leftJ rightJ)
            (sourceDistance source leftJ rightJ))
        literalToCovariance
        literalBound
  in
  ℚP.≤-trans covarianceToSourceEnvelope
    (sourceEnvelopeBelowSpectrumEnvelope source cutoff observable time)

------------------------------------------------------------------------
-- Continuum selected upper on the reconstructed covariance spectrum.
------------------------------------------------------------------------

literalTrajectorySourceBuildsSubgapUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  LiteralTrajectoryCMP116Source base demands tests spectrumSource →
  Gap.SubgapModeClusteringUpper (R281.asReconstructedClusteringSpectrum spectrumSource)
literalTrajectorySourceBuildsSubgapUpper
    {dataSet = dataSet} {extension = extension} {base = base}
    {tests = tests} {spectrumSource = spectrumSource} source
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
  in
  rationalUpperClosedUnderSelectedLimit source
    sequence target upper
    (R278.selectedConnectedCovarianceMagnitudeConverges
      extension tests index)
    (λ cutoff → finiteSelectedLiteralUpper source cutoff observable time)

------------------------------------------------------------------------
-- Introspective boundary.
------------------------------------------------------------------------

postHocSourceMagnitudeEqualityRequired : Bool
postHocSourceMagnitudeEqualityRequired = false

postHocSourceMagnitudeEqualityRequiredIsFalse :
  postHocSourceMagnitudeEqualityRequired ≡ false
postHocSourceMagnitudeEqualityRequiredIsFalse = refl

literalTrajectorySourceDirectProducer : Bool
literalTrajectorySourceDirectProducer = true

literalTrajectorySourceDirectProducerIsTrue :
  literalTrajectorySourceDirectProducer ≡ true
literalTrajectorySourceDirectProducerIsTrue = refl

record Round342Boundary : Set where
  constructor round342-boundary
  field
    postHocSourceMagnitudeEqualityIndependentLeaf : Bool
    postHocSourceMagnitudeEqualityIndependentLeafIsFalse :
      postHocSourceMagnitudeEqualityIndependentLeaf ≡ false

    commonDomainMembershipIndependentLeaf : Bool
    commonDomainMembershipIndependentLeafIsFalse :
      commonDomainMembershipIndependentLeaf ≡ false

    literalSelectedLocalizationStillProofBearing : Bool
    literalSelectedLocalizationStillProofBearingIsTrue :
      literalSelectedLocalizationStillProofBearing ≡ true

    sourceEnvelopeCalibrationStillProofBearing : Bool
    sourceEnvelopeCalibrationStillProofBearingIsTrue :
      sourceEnvelopeCalibrationStillProofBearing ≡ true

    oneSidedOrderClosureIsSharedAnalysis : Bool
    oneSidedOrderClosureIsSharedAnalysisIsTrue :
      oneSidedOrderClosureIsSharedAnalysis ≡ true

    freshYMDecayEstimateIntroduced : Bool
    freshYMDecayEstimateIntroducedIsFalse :
      freshYMDecayEstimateIntroduced ≡ false

canonicalRound342Boundary : Round342Boundary
canonicalRound342Boundary =
  round342-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl

round342LiteralSelectedLocalizationLevel : ProofLevel
round342LiteralSelectedLocalizationLevel = conditional

round342EnvelopeCalibrationLevel : ProofLevel
round342EnvelopeCalibrationLevel = conditional

round342OneSidedOrderClosureLevel : ProofLevel
round342OneSidedOrderClosureLevel = standardImported

round342CompilerLevel : ProofLevel
round342CompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
