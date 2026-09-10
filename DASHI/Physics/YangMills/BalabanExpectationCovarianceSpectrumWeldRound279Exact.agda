{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanExpectationCovarianceSpectrumWeldRound279Exact where

------------------------------------------------------------------------
-- ROUND279 / SAME-OBJECT COVARIANCE WELD
--
-- R278 already compiles selected expectation convergence for F, G and FG into
-- convergence of connected-covariance magnitudes.  The remaining continuum
-- work is semantic, not analytic:
--
--   finite RG covariance magnitude
--       == selected finite expectation covariance magnitude,
--
--   selected continuum expectation covariance magnitude
--       == exact reconstructed-spectrum connected correlation.
--
-- These equalities are proof-bearing fields on the exact observable/time
-- coordinates.  Naming both quantities "covariance" is not enough.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayOneSidedCorrelationLimitRound276Exact as R276

record ExpectationCovarianceSpectrumWeld
    {Measure TestObservable Scalar SpectralObservable Energy : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (spectrum : Gap.ReconstructedClusteringSpectrum SpectralObservable Energy Scalar)
    : Set₁ where
  field
    orderLimit : R276.UpperClosedConvergence Scalar

    orderLimitConvergenceIsScalarConvergence :
      (sequence : Nat → Scalar) (target : Scalar) →
      R276.Converges orderLimit sequence target
      ≡ Gram.Converges (Gram.scalarConvergence dataSet) sequence target

    convergenceCongruent :
      (first second : Nat → Scalar) (target : Scalar) →
      (∀ cutoff → first cutoff ≡ second cutoff) →
      Gram.Converges (Gram.scalarConvergence dataSet) first target →
      Gram.Converges (Gram.scalarConvergence dataSet) second target

    indexFor : SpectralObservable → Nat → R278.Index tests

    finiteRGCovariance : Nat → SpectralObservable → Nat → ℚ
    embed : ℚ → Scalar

    -- SAME finite object: the exact magnitude compiled from selected
    -- expectations is the embedded finite RG covariance magnitude.
    expectationMagnitudeIsEmbeddedFiniteRG : ∀ cutoff observable time →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        (R278.left tests (indexFor observable time))
        (R278.right tests (indexFor observable time))
      ≡ embed ∣ finiteRGCovariance cutoff observable time ∣

    -- SAME continuum object: the selected expectation covariance magnitude is
    -- exactly the correlation consumed by the reconstructed spectral theorem.
    continuumMagnitudeIsSpectrumCorrelation : ∀ observable time →
      R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        (R278.left tests (indexFor observable time))
        (R278.right tests (indexFor observable time))
      ≡ Gap.connectedCorrelation spectrum observable time

open ExpectationCovarianceSpectrumWeld public

embeddedFiniteRGConvergesToContinuumMagnitude :
  ∀ {Measure TestObservable Scalar SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrum : Gap.ReconstructedClusteringSpectrum SpectralObservable Energy Scalar}
    (weld : ExpectationCovarianceSpectrumWeld dataSet extension tests spectrum)
    observable time →
  Gram.Converges (Gram.scalarConvergence dataSet)
    (λ cutoff → embed weld ∣ finiteRGCovariance weld cutoff observable time ∣)
    (R278.connectedCovarianceMagnitude extension
      (Gram.continuumMeasure dataSet)
      (R278.left tests (indexFor weld observable time))
      (R278.right tests (indexFor weld observable time)))
embeddedFiniteRGConvergesToContinuumMagnitude
    {dataSet = dataSet} {extension = extension} {tests = tests}
    weld observable time =
  let
    index = indexFor weld observable time
    expectationSequence = λ cutoff →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        (R278.left tests index) (R278.right tests index)
    embeddedSequence = λ cutoff →
      embed weld ∣ finiteRGCovariance weld cutoff observable time ∣
    continuumMagnitude =
      R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        (R278.left tests index) (R278.right tests index)
    base = R278.selectedConnectedCovarianceMagnitudeConverges
      extension tests index
  in
  convergenceCongruent weld
    expectationSequence embeddedSequence continuumMagnitude
    (expectationMagnitudeIsEmbeddedFiniteRG weld
      (λ cutoff → cutoff) observable time)
    base

embeddedFiniteRGConvergesToSpectrumCorrelationScalar :
  ∀ {Measure TestObservable Scalar SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrum : Gap.ReconstructedClusteringSpectrum SpectralObservable Energy Scalar}
    (weld : ExpectationCovarianceSpectrumWeld dataSet extension tests spectrum)
    observable time →
  Gram.Converges (Gram.scalarConvergence dataSet)
    (λ cutoff → embed weld ∣ finiteRGCovariance weld cutoff observable time ∣)
    (Gap.connectedCorrelation spectrum observable time)
embeddedFiniteRGConvergesToSpectrumCorrelationScalar
    {dataSet = dataSet} {extension = extension} {tests = tests}
    {spectrum = spectrum} weld observable time =
  subst
    (λ target →
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff → embed weld ∣ finiteRGCovariance weld cutoff observable time ∣)
        target)
    (continuumMagnitudeIsSpectrumCorrelation weld observable time)
    (embeddedFiniteRGConvergesToContinuumMagnitude weld observable time)

embeddedFiniteRGConvergesToSpectrumCorrelation :
  ∀ {Measure TestObservable Scalar SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrum : Gap.ReconstructedClusteringSpectrum SpectralObservable Energy Scalar}
    (weld : ExpectationCovarianceSpectrumWeld dataSet extension tests spectrum)
    observable time →
  R276.Converges (orderLimit weld)
    (λ cutoff → embed weld ∣ finiteRGCovariance weld cutoff observable time ∣)
    (Gap.connectedCorrelation spectrum observable time)
embeddedFiniteRGConvergesToSpectrumCorrelation
    {dataSet = dataSet} {spectrum = spectrum} weld observable time =
  subst
    (λ proposition → proposition)
    (sym (orderLimitConvergenceIsScalarConvergence weld
      (λ cutoff → embed weld ∣ finiteRGCovariance weld cutoff observable time ∣)
      (Gap.connectedCorrelation spectrum observable time)))
    (embeddedFiniteRGConvergesToSpectrumCorrelationScalar weld observable time)

record Round279Boundary : Set where
  constructor round279-boundary
  field
    covarianceConvergenceNewYMAnalysis : Bool
    covarianceConvergenceNewYMAnalysisIsFalse :
      covarianceConvergenceNewYMAnalysis ≡ false

    finiteRGExpectationSameObjectRequired : Bool
    finiteRGExpectationSameObjectRequiredIsTrue :
      finiteRGExpectationSameObjectRequired ≡ true

    continuumExpectationSpectrumSameObjectRequired : Bool
    continuumExpectationSpectrumSameObjectRequiredIsTrue :
      continuumExpectationSpectrumSameObjectRequired ≡ true

canonicalRound279Boundary : Round279Boundary
canonicalRound279Boundary =
  round279-boundary false refl true refl true refl

round279ExpectationCovarianceSpectrumCompilerLevel : ProofLevel
round279ExpectationCovarianceSpectrumCompilerLevel = machineChecked

round279ConvergenceCongruenceLevel : ProofLevel
round279ConvergenceCongruenceLevel = standardImported

round279FiniteRGExpectationSameObjectLevel : ProofLevel
round279FiniteRGExpectationSameObjectLevel = conditional

round279ContinuumExpectationSpectrumSameObjectLevel : ProofLevel
round279ContinuumExpectationSpectrumSameObjectLevel = conditional
