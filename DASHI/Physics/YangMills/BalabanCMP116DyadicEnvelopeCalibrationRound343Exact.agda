{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116DyadicEnvelopeCalibrationRound343Exact where

------------------------------------------------------------------------
-- ROUND343 / DYADIC CALIBRATION PRODUCER FOR THE LITERAL R342 SOURCE
--
-- R342 deliberately keeps the source-native envelope generic.  On the direct
-- B route, however, the selected continuum upper is the concrete envelope
--
--      (1/4) (1/2)^time.
--
-- The existing source-exponential compiler already proves
--
--      shellValue(d) <= amplitude (1/2)^d
--
-- once the positive source exponent has been coarsened to a per-shell factor
-- q <= 1/2.  Therefore the concrete application does NOT need an arbitrary
-- pointwise theorem `sourceEnvelope <= spectrumEnvelope`.
--
-- The least-privilege calibration coordinates are only:
--   * the selected source envelope is the owned source shell at its distance;
--   * that selected source distance is the spectral time;
--   * source amplitude <= 1/4;
--   * the chosen spectrum envelope is exactly (1/4)(1/2)^time.
--
-- Everything between those coordinates is ordered-rational/compiler algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116LiteralTrajectorySourceRound342Exact as R342
import DASHI.Physics.YangMills.BalabanExponentialToDyadicShellCoarseningExact as Dyadic
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record DyadicLiteralTrajectoryCMP116Source
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

    literalSelectedDifferentiatedLocalization :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
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

    dyadicMajorant : Dyadic.SourceExponentialShellMajorant

    selectedSourceEnvelopeIsDyadicShell :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
        distance = sourceDistance leftJ rightJ
      in
      sourceEnvelope cutoff
        (sourceRoot cutoff leftJ rightJ) distance
      ≡ Dyadic.shellValue dyadicMajorant distance

    selectedSourceDistanceIsTime :
      ∀ observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      sourceDistance leftJ rightJ ≡ time

    sourceAmplitudeBelowQuarter :
      Dyadic.amplitude dyadicMajorant ≤ Shell.quarter

    spectrumEnvelopeIsQuarterHalfPower :
      ∀ observable time →
      R281.clusteringEnvelope spectrumSource observable time
      ≡ Shell.quarter * Geo.halfPower time

    rationalUpperClosedUnderSelectedLimit :
      (sequence : Nat → ℚ) (target upper : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open DyadicLiteralTrajectoryCMP116Source public

dyadicSourceEnvelopeBelowSpectrumEnvelope :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  (source : DyadicLiteralTrajectoryCMP116Source
    base demands tests spectrumSource) →
  ∀ cutoff observable time →
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
  in
  sourceEnvelope source cutoff
    (sourceRoot source cutoff leftJ rightJ)
    (sourceDistance source leftJ rightJ)
  ≤ R281.clusteringEnvelope spectrumSource observable time
dyadicSourceEnvelopeBelowSpectrumEnvelope
    {base = base} {tests = tests} {spectrumSource = spectrumSource}
    source cutoff observable time =
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
    distance = sourceDistance source leftJ rightJ

    shellBound :
      Dyadic.shellValue (dyadicMajorant source) distance
      ≤ Dyadic.amplitude (dyadicMajorant source) * Geo.halfPower distance
    shellBound = Dyadic.sourceExponentialShellIsDyadic
      (dyadicMajorant source) distance

    atTime :
      Dyadic.shellValue (dyadicMajorant source) distance
      ≤ Dyadic.amplitude (dyadicMajorant source) * Geo.halfPower time
    atTime = subst
      (λ selectedTime →
        Dyadic.shellValue (dyadicMajorant source) distance
        ≤ Dyadic.amplitude (dyadicMajorant source) * Geo.halfPower selectedTime)
      (selectedSourceDistanceIsTime source observable time)
      shellBound

    scaledAmplitude :
      Geo.halfPower time * Dyadic.amplitude (dyadicMajorant source)
      ≤ Geo.halfPower time * Shell.quarter
    scaledAmplitude = Norm.scaleNonnegative
      (Geo.halfPower time)
      (Geo.halfPowerNonnegative time)
      (sourceAmplitudeBelowQuarter source)

    rightAdjusted :
      Geo.halfPower time * Dyadic.amplitude (dyadicMajorant source)
      ≤ Shell.quarter * Geo.halfPower time
    rightAdjusted = subst
      (λ rightProduct →
        Geo.halfPower time * Dyadic.amplitude (dyadicMajorant source)
        ≤ rightProduct)
      (ℚP.*-comm (Geo.halfPower time) Shell.quarter)
      scaledAmplitude

    amplitudeBound :
      Dyadic.amplitude (dyadicMajorant source) * Geo.halfPower time
      ≤ Shell.quarter * Geo.halfPower time
    amplitudeBound = subst
      (λ leftProduct →
        leftProduct ≤ Shell.quarter * Geo.halfPower time)
      (ℚP.*-comm (Geo.halfPower time)
        (Dyadic.amplitude (dyadicMajorant source)))
      rightAdjusted

    sourceEnvelopeToAmplitude :
      sourceEnvelope source cutoff
        (sourceRoot source cutoff leftJ rightJ) distance
      ≤ Dyadic.amplitude (dyadicMajorant source) * Geo.halfPower time
    sourceEnvelopeToAmplitude = subst
      (λ lower →
        lower ≤ Dyadic.amplitude (dyadicMajorant source) * Geo.halfPower time)
      (sym (selectedSourceEnvelopeIsDyadicShell source cutoff observable time))
      atTime

    sourceToQuarter :
      sourceEnvelope source cutoff
        (sourceRoot source cutoff leftJ rightJ) distance
      ≤ Shell.quarter * Geo.halfPower time
    sourceToQuarter = ℚP.≤-trans sourceEnvelopeToAmplitude amplitudeBound
  in
  subst
    (λ upper →
      sourceEnvelope source cutoff
        (sourceRoot source cutoff leftJ rightJ) distance
      ≤ upper)
    (sym (spectrumEnvelopeIsQuarterHalfPower source observable time))
    sourceToQuarter

asLiteralTrajectoryCMP116Source :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  DyadicLiteralTrajectoryCMP116Source base demands tests spectrumSource →
  R342.LiteralTrajectoryCMP116Source base demands tests spectrumSource
asLiteralTrajectoryCMP116Source source = record
  { R342.LiteralTrajectoryCMP116Source.sourceRoot = sourceRoot source
  ; R342.LiteralTrajectoryCMP116Source.sourceDistance = sourceDistance source
  ; R342.LiteralTrajectoryCMP116Source.sourceEnvelope = sourceEnvelope source
  ; R342.LiteralTrajectoryCMP116Source.SourceEnvelopeHasPositiveExponentialTreeDecay =
      SourceEnvelopeHasPositiveExponentialTreeDecay source
  ; R342.LiteralTrajectoryCMP116Source.sourceEnvelopeHasPositiveExponentialTreeDecay =
      sourceEnvelopeHasPositiveExponentialTreeDecay source
  ; R342.LiteralTrajectoryCMP116Source.literalSelectedDifferentiatedLocalization =
      literalSelectedDifferentiatedLocalization source
  ; R342.LiteralTrajectoryCMP116Source.sourceEnvelopeBelowSpectrumEnvelope =
      dyadicSourceEnvelopeBelowSpectrumEnvelope source
  ; R342.LiteralTrajectoryCMP116Source.rationalUpperClosedUnderSelectedLimit =
      rationalUpperClosedUnderSelectedLimit source
  }

pointwiseEnvelopeComparisonPrimitive : Bool
pointwiseEnvelopeComparisonPrimitive = false

pointwiseEnvelopeComparisonPrimitiveIsFalse :
  pointwiseEnvelopeComparisonPrimitive ≡ false
pointwiseEnvelopeComparisonPrimitiveIsFalse = refl

dyadicCalibrationBuildsR342Source : Bool
dyadicCalibrationBuildsR342Source = true

dyadicCalibrationBuildsR342SourceIsTrue :
  dyadicCalibrationBuildsR342Source ≡ true
dyadicCalibrationBuildsR342SourceIsTrue = refl

dyadicCalibrationUsesOnlyShellDistanceAmplitude : Bool
dyadicCalibrationUsesOnlyShellDistanceAmplitude = true

dyadicCalibrationUsesOnlyShellDistanceAmplitudeIsTrue :
  dyadicCalibrationUsesOnlyShellDistanceAmplitude ≡ true
dyadicCalibrationUsesOnlyShellDistanceAmplitudeIsTrue = refl

record Round343Boundary : Set where
  constructor round343-boundary
  field
    arbitraryPointwiseEnvelopeComparisonIndependentLeaf : Bool
    arbitraryPointwiseEnvelopeComparisonIndependentLeafIsFalse :
      arbitraryPointwiseEnvelopeComparisonIndependentLeaf ≡ false

    sourceExponentialToDyadicCompilerOwned : Bool
    sourceExponentialToDyadicCompilerOwnedIsTrue :
      sourceExponentialToDyadicCompilerOwned ≡ true

    selectedShellSameObjectStillProofBearing : Bool
    selectedShellSameObjectStillProofBearingIsTrue :
      selectedShellSameObjectStillProofBearing ≡ true

    selectedDistanceTimeStillProofBearing : Bool
    selectedDistanceTimeStillProofBearingIsTrue :
      selectedDistanceTimeStillProofBearing ≡ true

    amplitudeQuarterStillProofBearing : Bool
    amplitudeQuarterStillProofBearingIsTrue :
      amplitudeQuarterStillProofBearing ≡ true

canonicalRound343Boundary : Round343Boundary
canonicalRound343Boundary =
  round343-boundary false refl true refl true refl true refl true refl

round343DyadicCompilerLevel : ProofLevel
round343DyadicCompilerLevel = machineChecked

round343SelectedShellSameObjectLevel : ProofLevel
round343SelectedShellSameObjectLevel = conditional

round343SelectedDistanceTimeLevel : ProofLevel
round343SelectedDistanceTimeLevel = conditional

round343AmplitudeQuarterLevel : ProofLevel
round343AmplitudeQuarterLevel = conditional
