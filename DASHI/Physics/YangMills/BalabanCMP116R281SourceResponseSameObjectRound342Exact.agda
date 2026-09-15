{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact where

------------------------------------------------------------------------
-- ROUND342 / ISOLATE THE CURRENT T78-B SAME-OBJECT RESPONSE PAYMENT
--
-- R341 reduced the preferred source-native T78-B route to two physical/source
-- coordinates plus standard one-sided order closure:
--
--   B1. CMP116 differentiated source-response magnitude
--       = selected literal mixed-log magnitude;
--   B2. CMP116 source envelope <= selected spectral clustering envelope.
--
-- This owner isolates B1 as a standalone same-object witness.  It does not
-- weaken B2, does not introduce a new decay estimate, and does not infer the
-- source identity from citation/provenance.  Supplying B1, B2, and the standard
-- R278 order-closure theorem mechanically reconstructs the existing R341
-- application.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341

------------------------------------------------------------------------
-- B1 only.
------------------------------------------------------------------------

record SourceResponseSameObjectPayment
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

open SourceResponseSameObjectPayment public

------------------------------------------------------------------------
-- Keep B2 independent.
------------------------------------------------------------------------

SourceEnvelopeCalibration :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    (source : R338.CanonicalCommonDomainCMP116Source base demands)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests) →
  Set
SourceEnvelopeCalibration base demands source tests spectrumSource =
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

SelectedLimitUpperClosure :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ} →
  Set
SelectedLimitUpperClosure {dataSet = dataSet} =
  (sequence : Nat → ℚ) (target upper : ℚ) →
  Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
  (∀ cutoff → sequence cutoff ≤ upper) →
  target ≤ upper

------------------------------------------------------------------------
-- Compiler back into the existing R341 application.
------------------------------------------------------------------------

asRound341Application :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests} →
  SourceResponseSameObjectPayment base demands source tests spectrumSource →
  SourceEnvelopeCalibration base demands source tests spectrumSource →
  SelectedLimitUpperClosure {dataSet = dataSet} →
  R341.CanonicalCMP116R281ModeSelectedApplication
    base demands source tests spectrumSource
asRound341Application b1 b2 limitClosure = record
  { R341.CanonicalCMP116R281ModeSelectedApplication.sourceMagnitudeIsSelectedMixedLogMagnitude =
      sourceMagnitudeIsSelectedMixedLogMagnitude b1
  ; R341.CanonicalCMP116R281ModeSelectedApplication.sourceEnvelopeBelowSpectrumEnvelope =
      b2
  ; R341.CanonicalCMP116R281ModeSelectedApplication.rationalUpperClosedUnderSelectedLimit =
      limitClosure
  }

round342CompilerLevel : ProofLevel
round342CompilerLevel = machineChecked

-- B1 remains the physical/source same-object payment.
round342SourceResponseSameObjectLevel : ProofLevel
round342SourceResponseSameObjectLevel = conditional

-- B2 remains an independent quantitative calibration payment.
round342EnvelopeCalibrationLevel : ProofLevel
round342EnvelopeCalibrationLevel = conditional

-- Generic ordered-limit closure remains source-independent standard analysis.
round342SelectedLimitUpperClosureLevel : ProofLevel
round342SelectedLimitUpperClosureLevel =
  R341.round341OneSidedOrderClosureLevel

freshYMDecayEstimateIntroduced : Bool
freshYMDecayEstimateIntroduced = false

clayPromotion : Bool
clayPromotion = false
