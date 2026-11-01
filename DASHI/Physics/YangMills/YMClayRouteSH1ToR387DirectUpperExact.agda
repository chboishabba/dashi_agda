{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSH1ToR387DirectUpperExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact as R387
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.YMClayRouteSH1DirectSelectedMarkedDecayExact as H1

------------------------------------------------------------------------
-- CANONICAL ROUTE-S SOURCE SEGMENT: H1 -> R387
--
-- H1 itself is only R320's one selected-carrier localization theorem.
-- To reach the terminal R387 upper, two semantically distinct facts are needed:
--
--   T: the selected pair's physical support distance is Euclidean time;
--   E: the selected spectrum's fast clustering envelope is the rooted
--      quarter/half geometric envelope used by the finite source theorem.
--
-- Neither is folded into H1.  T belongs to the Euclidean/OS application
-- semantics and E belongs to the selected spectral-rate presentation.
--
-- Given H1 + T + E, every inequality between them is existing compiler algebra.
------------------------------------------------------------------------

record RouteSH1TerminalCalibration
    {Measure TestObservable SpectralObservable Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable}
      {Energy = Energy}
      dataSet extension tests)
    : Set₁ where
  field
    h1 : H1.RouteSH1DirectSelectedPayment base

    selectedPairDistanceIsTime :
      ∀ observable time →
      let index = R281.indexFor spectrumSource observable time in
      R318.physicalDistance base
        (R278.left tests index)
        (R278.right tests index)
      ≡ time

    spectrumEnvelopeIsRootedGeometric :
      ∀ observable time →
      R281.clusteringEnvelope spectrumSource observable time
      ≡ Shell.quarter * Power.rationalPower Geo.half time

open RouteSH1TerminalCalibration public

selectedMixedDerivativeBelowRootedGeometric :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable}
      {Energy = Energy}
      dataSet extension tests} →
  (calibration : RouteSH1TerminalCalibration base tests spectrumSource) →
  ∀ cutoff observable time →
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
  in
  R278.magnitude extension
    (Cumulant.literalMixedSecondLogDerivative
      (R318.meaning base)
      (Cumulant.sourceDirectionOf
        (R318.meaning base) left)
      (Cumulant.sourceDirectionOf
        (R318.meaning base) right)
      cutoff)
  ≤ Shell.quarter * Power.rationalPower Geo.half time
selectedMixedDerivativeBelowRootedGeometric
    {base = base} {tests = tests} {spectrumSource = spectrumSource}
    calibration cutoff observable time =
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    payment = H1.directSelectedDecay (h1 calibration)

    shellBound =
      R320.literalSelectedJMagnitudeBelowShell payment cutoff left right

    rootedBound =
      Shell.rootedShellBelowQuarterHalfPower
        (R318.shellData base)
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (R318.connectingRoot base cutoff left right)
        (R318.physicalDistance base left right)

    combined =
      ℚP.≤-trans shellBound rootedBound

    exposeRationalPower =
      R274.halfPowerIsRationalPower (R318.physicalDistance base left right)

    rationalized =
      subst
        (λ power →
          R278.magnitude extension
            (Cumulant.literalMixedSecondLogDerivative
              (R318.meaning base)
              (Cumulant.sourceDirectionOf
                (R318.meaning base) left)
              (Cumulant.sourceDirectionOf
                (R318.meaning base) right)
              cutoff)
          ≤ Shell.quarter * power)
        exposeRationalPower
        combined
  in
  subst
    (λ distance →
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative
          (R318.meaning base)
          (Cumulant.sourceDirectionOf
            (R318.meaning base) left)
          (Cumulant.sourceDirectionOf
            (R318.meaning base) right)
          cutoff)
      ≤ Shell.quarter * Power.rationalPower Geo.half distance)
    (selectedPairDistanceIsTime calibration observable time)
    rationalized

h1CalibrationBuildsR387DirectUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable}
      {Energy = Energy}
      dataSet extension tests} →
  RouteSH1TerminalCalibration base tests spectrumSource →
  R387.DirectSelectedSpectralUpper base tests spectrumSource
h1CalibrationBuildsR387DirectUpper
    {extension = extension} {base = base}
    {tests = tests} {spectrumSource = spectrumSource}
    calibration = record
  { R387.DirectSelectedSpectralUpper.selectedResponseBelowSpectrumEnvelope =
      λ cutoff observable time →
        let
          index = R281.indexFor spectrumSource observable time
          left = R278.left tests index
          right = R278.right tests index
        in
        subst
          (λ upper →
            R278.magnitude extension
              (Cumulant.literalMixedSecondLogDerivative
                (R318.meaning base)
                (Cumulant.sourceDirectionOf (R318.meaning base) left)
                (Cumulant.sourceDirectionOf (R318.meaning base) right)
                cutoff)
            ≤ upper)
          (sym (spectrumEnvelopeIsRootedGeometric
            calibration observable time))
          (selectedMixedDerivativeBelowRootedGeometric
            calibration cutoff observable time)
  }

------------------------------------------------------------------------
-- Pareto classification.
------------------------------------------------------------------------

sourceEnvelopeRequiredBetweenH1AndR387 : Bool
sourceEnvelopeRequiredBetweenH1AndR387 = false

sourceEnvelopeRequiredBetweenH1AndR387IsFalse :
  sourceEnvelopeRequiredBetweenH1AndR387 ≡ false
sourceEnvelopeRequiredBetweenH1AndR387IsFalse = refl

sourceRootOrDistanceCarrierRequiredBetweenH1AndR387 : Bool
sourceRootOrDistanceCarrierRequiredBetweenH1AndR387 = false

sourceRootOrDistanceCarrierRequiredBetweenH1AndR387IsFalse :
  sourceRootOrDistanceCarrierRequiredBetweenH1AndR387 ≡ false
sourceRootOrDistanceCarrierRequiredBetweenH1AndR387IsFalse = refl

selectedTimeMeaningRemainsOutsideH1 : Bool
selectedTimeMeaningRemainsOutsideH1 = true

selectedTimeMeaningRemainsOutsideH1IsTrue :
  selectedTimeMeaningRemainsOutsideH1 ≡ true
selectedTimeMeaningRemainsOutsideH1IsTrue = refl

selectedFastEnvelopeMeaningRemainsOutsideH1 : Bool
selectedFastEnvelopeMeaningRemainsOutsideH1 = true

selectedFastEnvelopeMeaningRemainsOutsideH1IsTrue :
  selectedFastEnvelopeMeaningRemainsOutsideH1 ≡ true
selectedFastEnvelopeMeaningRemainsOutsideH1IsTrue = refl

h1ToR387CompilerLevel : ProofLevel
h1ToR387CompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
