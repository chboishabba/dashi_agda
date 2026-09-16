{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SharedMarkedDirectCalibrationRound344Exact where

------------------------------------------------------------------------
-- ROUND344 / ACTUAL SHARED-MARKED CMP116 CARRIER -> R342
--
-- The generic R343 source-exponential carrier is useful for alternative
-- producers, but the actual shared CMP116 marked shell already owns the exact
-- geometric theorem
--
--   markedAnalyticShell(hessianMark,d)
--     <= (1/4 * C_H) * (1/2)^d.
--
-- Therefore this source-native direct producer needs no extra exponential-shell
-- repackaging.  On the selected B consumer it leaves only:
--
--   * the literal selected differentiated localization theorem;
--   * selected physical source distance = Euclidean spectral time;
--   * C_H <= 1;
--
-- plus the choice that the reconstructed spectrum uses the canonical
-- (1/4)(1/2)^time envelope.  The latter is a presentation choice, not a new YM
-- estimate.  Ordered finite->continuum closure remains shared analysis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _*_; _≤_)
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
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geometric
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record SharedMarkedDirectCMP116Source
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
    shared : Shared.SharedMarkedAnalyticShellControl
      (R318.Scale base) (R318.Volume base) (R318.Root base)

    sourceRoot :
      Nat → R318.SourceDirection base → R318.SourceDirection base → R318.Root base

    sourceDistance :
      R318.SourceDirection base → R318.SourceDirection base → Nat

    -- The one source/application theorem, already on the literal selected
    -- mixed-log response and the actual shared hessian-mark shell.
    literalSelectedDifferentiatedLocalization :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
        root = sourceRoot cutoff leftJ rightJ
        distance = sourceDistance leftJ rightJ
      in
      Common.SourceCoordinateInside
        (R114.canonicalCMP116CommonDomain
          {R318.Scale base} {R318.Volume base} demands)
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff) →
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
          leftJ rightJ cutoff)
      ≤ Shared.markedAnalyticShell shared Shared.hessianMark
          (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
          root distance

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

    hessianAnalyticConstantAtMostOne :
      Shared.hessianAnalyticConstant shared ≤ 1ℚ

    spectrumEnvelopeIsQuarterHalfPower :
      ∀ observable time →
      R281.clusteringEnvelope spectrumSource observable time
      ≡ Shell.quarter * Geo.halfPower time

    rationalUpperClosedUnderSelectedLimit :
      (sequence : Nat → ℚ) (target upper : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open SharedMarkedDirectCMP116Source public

markedBaseEnergyBelowQuarter :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  (source : SharedMarkedDirectCMP116Source
    base demands tests spectrumSource) →
  Geometric.markedBaseEnergy (shared source) Shared.hessianMark ≤ Shell.quarter
markedBaseEnergyBelowQuarter source =
  let
    scaled :
      Shell.quarter * Shared.hessianAnalyticConstant (shared source)
      ≤ Shell.quarter * 1ℚ
    scaled = Norm.scaleNonnegative
      Shell.quarter
      Geometric.quarterNN
      (hessianAnalyticConstantAtMostOne source)
  in
  subst
    (λ upper →
      Geometric.markedBaseEnergy (shared source) Shared.hessianMark ≤ upper)
    (ℚP.*-identityʳ Shell.quarter)
    scaled

sharedMarkedEnvelopeBelowSpectrumEnvelope :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  (source : SharedMarkedDirectCMP116Source
    base demands tests spectrumSource) →
  ∀ cutoff observable time →
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
    root = sourceRoot source cutoff leftJ rightJ
    distance = sourceDistance source leftJ rightJ
  in
  Shared.markedAnalyticShell (shared source) Shared.hessianMark
    (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
    root distance
  ≤ R281.clusteringEnvelope spectrumSource observable time
sharedMarkedEnvelopeBelowSpectrumEnvelope
    {base = base} {tests = tests} {spectrumSource = spectrumSource}
    source cutoff observable time =
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
    root = sourceRoot source cutoff leftJ rightJ
    distance = sourceDistance source leftJ rightJ

    geometric :
      Shared.markedAnalyticShell (shared source) Shared.hessianMark
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
        root distance
      ≤ Geometric.markedBaseEnergy (shared source) Shared.hessianMark
          * Geo.halfPower distance
    geometric = Geometric.markedAnalyticShellGeometricHalf
      (shared source) Shared.hessianMark
      (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
      root distance

    atTime :
      Shared.markedAnalyticShell (shared source) Shared.hessianMark
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
        root distance
      ≤ Geometric.markedBaseEnergy (shared source) Shared.hessianMark
          * Geo.halfPower time
    atTime = subst
      (λ selectedTime →
        Shared.markedAnalyticShell (shared source) Shared.hessianMark
          (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
          root distance
        ≤ Geometric.markedBaseEnergy (shared source) Shared.hessianMark
            * Geo.halfPower selectedTime)
      (selectedSourceDistanceIsTime source observable time)
      geometric

    scaledBase :
      Geo.halfPower time
        * Geometric.markedBaseEnergy (shared source) Shared.hessianMark
      ≤ Geo.halfPower time * Shell.quarter
    scaledBase = Norm.scaleNonnegative
      (Geo.halfPower time)
      (Geo.halfPowerNonnegative time)
      (markedBaseEnergyBelowQuarter source)

    rightAdjusted :
      Geo.halfPower time
        * Geometric.markedBaseEnergy (shared source) Shared.hessianMark
      ≤ Shell.quarter * Geo.halfPower time
    rightAdjusted = subst
      (λ rightProduct →
        Geo.halfPower time
          * Geometric.markedBaseEnergy (shared source) Shared.hessianMark
        ≤ rightProduct)
      (ℚP.*-comm (Geo.halfPower time) Shell.quarter)
      scaledBase

    baseBound :
      Geometric.markedBaseEnergy (shared source) Shared.hessianMark
        * Geo.halfPower time
      ≤ Shell.quarter * Geo.halfPower time
    baseBound = subst
      (λ leftProduct → leftProduct ≤ Shell.quarter * Geo.halfPower time)
      (ℚP.*-comm (Geo.halfPower time)
        (Geometric.markedBaseEnergy (shared source) Shared.hessianMark))
      rightAdjusted

    toQuarter :
      Shared.markedAnalyticShell (shared source) Shared.hessianMark
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
        root distance
      ≤ Shell.quarter * Geo.halfPower time
    toQuarter = ℚP.≤-trans atTime baseBound
  in
  subst
    (λ upper →
      Shared.markedAnalyticShell (shared source) Shared.hessianMark
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
        root distance
      ≤ upper)
    (sym (spectrumEnvelopeIsQuarterHalfPower source observable time))
    toQuarter

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
  SharedMarkedDirectCMP116Source base demands tests spectrumSource →
  R342.LiteralTrajectoryCMP116Source base demands tests spectrumSource
asLiteralTrajectoryCMP116Source
    {base = base} source = record
  { R342.LiteralTrajectoryCMP116Source.sourceRoot = sourceRoot source
  ; R342.LiteralTrajectoryCMP116Source.sourceDistance = sourceDistance source
  ; R342.LiteralTrajectoryCMP116Source.sourceEnvelope =
      λ cutoff root depth →
        Shared.markedAnalyticShell (shared source) Shared.hessianMark
          (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
          root depth
  ; R342.LiteralTrajectoryCMP116Source.SourceEnvelopeHasPositiveExponentialTreeDecay =
      ∀ cutoff root depth →
        Shared.markedAnalyticShell (shared source) Shared.hessianMark
          (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
          root depth
        ≤ Geometric.markedBaseEnergy (shared source) Shared.hessianMark
            * Geo.halfPower depth
  ; R342.LiteralTrajectoryCMP116Source.sourceEnvelopeHasPositiveExponentialTreeDecay =
      λ cutoff root depth →
        Geometric.markedAnalyticShellGeometricHalf
          (shared source) Shared.hessianMark
          (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
          root depth
  ; R342.LiteralTrajectoryCMP116Source.literalSelectedDifferentiatedLocalization =
      literalSelectedDifferentiatedLocalization source
  ; R342.LiteralTrajectoryCMP116Source.sourceEnvelopeBelowSpectrumEnvelope =
      sharedMarkedEnvelopeBelowSpectrumEnvelope source
  ; R342.LiteralTrajectoryCMP116Source.rationalUpperClosedUnderSelectedLimit =
      rationalUpperClosedUnderSelectedLimit source
  }

genericExponentialShellRepackagingMandatory : Bool
genericExponentialShellRepackagingMandatory = false

genericExponentialShellRepackagingMandatoryIsFalse :
  genericExponentialShellRepackagingMandatory ≡ false
genericExponentialShellRepackagingMandatoryIsFalse = refl

sharedMarkedDirectBuildsR342Source : Bool
sharedMarkedDirectBuildsR342Source = true

sharedMarkedDirectBuildsR342SourceIsTrue :
  sharedMarkedDirectBuildsR342Source ≡ true
sharedMarkedDirectBuildsR342SourceIsTrue = refl

onlyLocalizationDistanceConstantRemain : Bool
onlyLocalizationDistanceConstantRemain = true

onlyLocalizationDistanceConstantRemainIsTrue :
  onlyLocalizationDistanceConstantRemain ≡ true
onlyLocalizationDistanceConstantRemainIsTrue = refl

record Round344Boundary : Set where
  constructor round344-boundary
  field
    genericExponentialCarrierMandatory : Bool
    genericExponentialCarrierMandatoryIsFalse :
      genericExponentialCarrierMandatory ≡ false

    sharedMarkedGeometricHalfCompilerOwned : Bool
    sharedMarkedGeometricHalfCompilerOwnedIsTrue :
      sharedMarkedGeometricHalfCompilerOwned ≡ true

    literalSelectedLocalizationStillProofBearing : Bool
    literalSelectedLocalizationStillProofBearingIsTrue :
      literalSelectedLocalizationStillProofBearing ≡ true

    selectedDistanceTimeStillProofBearing : Bool
    selectedDistanceTimeStillProofBearingIsTrue :
      selectedDistanceTimeStillProofBearing ≡ true

    selectedHessianConstantAtMostOneStillProofBearing : Bool
    selectedHessianConstantAtMostOneStillProofBearingIsTrue :
      selectedHessianConstantAtMostOneStillProofBearing ≡ true

canonicalRound344Boundary : Round344Boundary
canonicalRound344Boundary =
  round344-boundary false refl true refl true refl true refl true refl

round344SharedMarkedCompilerLevel : ProofLevel
round344SharedMarkedCompilerLevel = machineChecked

round344LiteralSelectedLocalizationLevel : ProofLevel
round344LiteralSelectedLocalizationLevel = conditional

round344SelectedDistanceTimeLevel : ProofLevel
round344SelectedDistanceTimeLevel = conditional

round344HessianConstantAtMostOneLevel : ProofLevel
round344HessianConstantAtMostOneLevel = conditional
