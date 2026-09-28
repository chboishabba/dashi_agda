{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedGapExact where

------------------------------------------------------------------------
-- PHYSICAL REAL H1 -> SELECTED CONTINUUM GAP CORE.
--
-- The actual CMP119 continuum covariance is ℝ-valued.  Reuse the existing
-- LiteralRealCMP116ClusteringInputs theorem directly on that carrier, bind its
-- selected index/observables to the exact R281 tests, and calibrate its physical
-- upper to R281's clustering envelope.
--
-- This bypasses the historical rational R387 finite-to-continuum presentation:
-- no identification ℚ = ℝ and no second continuum system is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_; ≤ℝ-trans)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ClusteringExact as RealH1
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119RealSelectedSpectrumApplication
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState
     Scale Volume Root SourceDirection SpectralObservable Energy : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {S}
    (a :
      A.PinnedCMP119OSAxiomInputs
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : CompactSimpleGroup)
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ)
    : Set₂ where
  private
    dataSet = Carrier.cmp119PhysicalMeasureConvergenceData a group
    extension = Cov.realCovarianceExtension a covarianceLaws group

  field
    tests :
      R278.SelectedConnectedCovarianceTests dataSet

    spectrumSource :
      R281.ContinuumCovarianceSpectrumData
        {SpectralObservable = SpectralObservable}
        {Energy = Energy}
        dataSet extension tests

    realH1 :
      RealH1.LiteralRealCMP116ClusteringInputs
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian VacuumState
        Scale Volume Root SourceDirection
        (R278.Index tests)
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        a covarianceLaws group source

    selectedLeftIsH1Left :
      ∀ index →
      R278.left tests index ≡ RealH1.left realH1 index

    selectedRightIsH1Right :
      ∀ index →
      R278.right tests index ≡ RealH1.right realH1 index

    physicalUpperBelowSpectrumEnvelope :
      ∀ observable time →
      RealH1.physicalUpper realH1
        (R281.indexFor spectrumSource observable time)
      ≤ℝ
      R281.clusteringEnvelope spectrumSource observable time

    realOrderImpliesSpectrumOrder :
      ∀ left right →
      left ≤ℝ right →
      R281.LessEqual spectrumSource left right

open CMP119RealSelectedSpectrumApplication public

selectedContinuumCovarianceBelowSpectrumEnvelope :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection SpectralObservable Energy
      sequenceLimit limitLaws quotient division S
      a covarianceLaws group source}
    (application :
      CMP119RealSelectedSpectrumApplication
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection SpectralObservable Energy
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        a covarianceLaws group source)
    observable time →
  let
    tests = tests application
    spectrumSource = spectrumSource application
    index = R281.indexFor spectrumSource observable time
  in
  R281.LessEqual spectrumSource
    (R278.connectedCovarianceMagnitude
      (Cov.realCovarianceExtension a covarianceLaws group)
      (Gram.continuumMeasure
        (Carrier.cmp119PhysicalMeasureConvergenceData a group))
      (R278.left tests index)
      (R278.right tests index))
    (R281.clusteringEnvelope spectrumSource observable time)
selectedContinuumCovarianceBelowSpectrumEnvelope
    {a = a} {covarianceLaws = covarianceLaws} {group = group}
    application observable time =
  let
    tests' = tests application
    spectrum = spectrumSource application
    index = R281.indexFor spectrum observable time
    h1 = realH1 application

    h1Bound =
      RealH1.continuumPhysicalCovarianceBelowUpper h1 index

    selectedBound :
      R278.connectedCovarianceMagnitude
        (Cov.realCovarianceExtension a covarianceLaws group)
        (Gram.continuumMeasure
          (Carrier.cmp119PhysicalMeasureConvergenceData a group))
        (R278.left tests' index)
        (R278.right tests' index)
      ≤ℝ
      RealH1.physicalUpper h1 index
    selectedBound
      rewrite selectedLeftIsH1Left application index
            | selectedRightIsH1Right application index =
      h1Bound

    calibrated =
      physicalUpperBelowSpectrumEnvelope application observable time
  in
  realOrderImpliesSpectrumOrder application
    _
    _
    (≤ℝ-trans selectedBound calibrated)

selectedSubgapModeClusteringUpper :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection SpectralObservable Energy
      sequenceLimit limitLaws quotient division S
      a covarianceLaws group source}
    (application :
      CMP119RealSelectedSpectrumApplication
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection SpectralObservable Energy
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        a covarianceLaws group source) →
  Gap.SubgapModeClusteringUpper
    (R281.asReconstructedClusteringSpectrum
      (spectrumSource application))
selectedSubgapModeClusteringUpper application energy mode time =
  selectedContinuumCovarianceBelowSpectrumEnvelope application
    (R281.modeObservable (spectrumSource application) energy mode)
    time

positiveTransferGapCore :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection SpectralObservable Energy
      sequenceLimit limitLaws quotient division S
      a covarianceLaws group source}
    (application :
      CMP119RealSelectedSpectrumApplication
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection SpectralObservable Energy
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        a covarianceLaws group source) →
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum
      (spectrumSource application))
    (Gap.gapCandidate
      (R281.asReconstructedClusteringSpectrum
        (spectrumSource application))) →
  Gap.PositiveTransferGapCore
    (R281.asReconstructedClusteringSpectrum
      (spectrumSource application))
positiveTransferGapCore application positive =
  Gap.positiveTransferGapCoreFromModeTests
    (R281.asReconstructedClusteringSpectrum
      (spectrumSource application))
    (selectedSubgapModeClusteringUpper application)
    positive

cmp119RealSelectedGapCompilerLevel : ProofLevel
cmp119RealSelectedGapCompilerLevel = machineChecked

-- Actual physical payments are exactly those already visible in realH1,
-- selected-test same-object identification, envelope calibration, and the
-- spectral lower/rate semantics inside spectrumSource.
cmp119RealSelectedGapPhysicalInstantiationLevel : ProofLevel
cmp119RealSelectedGapPhysicalInstantiationLevel = conditional
