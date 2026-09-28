{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119RealSameOSH3Exact where

------------------------------------------------------------------------
-- H3 ON THE ACTUAL REAL CMP119 OS RECONSTRUCTION.
--
-- The physical Hamiltonian is NOT selected: it is definitionally the
-- Hamiltonian reconstructed from H2's exact CMP119 Schwinger system.
--
-- The sole spectral theorem is therefore:
--
--   no positive subgap mode for the R281 covariance spectrum
--     -> spectral separation of this exact reconstructed Hamiltonian.
--
-- Combined with the real H1/H2 clustering core, this constructs the physical
-- mass-gap certificate on the same OS Hamiltonian.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2Exact as H2
import DASHI.Physics.YangMills.YangMillsClayCMP119OSReconstructionAuthorityExact as H2OS
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedGapExact as RealGap
import DASHI.Physics.YangMills.YMClayMixedScalarPhysicalSpectrumExact as Mixed
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as OSR
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record CMP119RealSameOSH3
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     EuclideanAction Permutation Epsilon Witness
     Scale Volume Root SourceDirection SpectralObservable : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (S :
      Top.LiteralYangMillsSemantics
        (DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact.physicalLiteralCarriers
          G X Agda.Builtin.Nat.Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vector))
    (h2 :
      H2.CMP119DirectPhysicalH2
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : G)
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ)
    (application :
      RealGap.CMP119RealSelectedSpectrumApplication
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector
        Scale Volume Root SourceDirection SpectralObservable ℚ
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        (H2.osInputs h2) covarianceLaws group source)
    : Set₂ where
  private
    spectrum =
      R281.asReconstructedClusteringSpectrum
        (RealGap.spectrumSource application)

    actualHamiltonian =
      OSR.reconstructedHamiltonian
        (DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact.reconstruction
          (H2.reconstruction h2) group)

  field
    SpectrumAboveVacuumGap :
      Hamiltonian → ℚ → Set

    noPositiveSubgapMeansActualSpectrumSeparated :
      Gap.NoPositiveSubgapMode spectrum →
      SpectrumAboveVacuumGap
        actualHamiltonian
        (Gap.gapCandidate spectrum)

open CMP119RealSameOSH3 public

physicalSpectrumInterpretation :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable
      sequenceLimit limitLaws quotient division S
      h2 covarianceLaws group source application} →
  CMP119RealSameOSH3
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    Scale Volume Root SourceDirection SpectralObservable
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
    h2 covarianceLaws group source application →
  Mixed.MixedScalarPhysicalSpectrumInterpretation
    {Hamiltonian = Hamiltonian}
    (R281.asReconstructedClusteringSpectrum
      (RealGap.spectrumSource application))
physicalSpectrumInterpretation
    {h2 = h2} {group = group} {application = application}
    h3 = record
  { Mixed.MixedScalarPhysicalSpectrumInterpretation.physicalHamiltonian =
      OSR.reconstructedHamiltonian
        (DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact.reconstruction
          (H2.reconstruction h2) group)
  ; Mixed.MixedScalarPhysicalSpectrumInterpretation.SpectrumAboveVacuumGap =
      SpectrumAboveVacuumGap h3
  ; Mixed.MixedScalarPhysicalSpectrumInterpretation.noPositiveSubgapMeansSpectrumSeparated =
      noPositiveSubgapMeansActualSpectrumSeparated h3
  }

physicalMassGapCertificate :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable
      sequenceLimit limitLaws quotient division S
      h2 covarianceLaws group source application}
    (h3 :
      CMP119RealSameOSH3
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        Scale Volume Root SourceDirection SpectralObservable
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S
        h2 covarianceLaws group source application) →
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum
      (RealGap.spectrumSource application))
    (Gap.gapCandidate
      (R281.asReconstructedClusteringSpectrum
        (RealGap.spectrumSource application))) →
  OS.PhysicalMassGapCertificate Hamiltonian ℚ
physicalMassGapCertificate {application = application} h3 positive =
  Mixed.physicalMassGapCertificate
    (physicalSpectrumInterpretation h3)
    (RealGap.positiveTransferGapCore application positive)

h3PhysicalHamiltonianIsExactH2Reconstruction :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable
      sequenceLimit limitLaws quotient division S
      h2 covarianceLaws group source application}
    (h3 :
      CMP119RealSameOSH3
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        Scale Volume Root SourceDirection SpectralObservable
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S
        h2 covarianceLaws group source application) →
  Mixed.physicalHamiltonian (physicalSpectrumInterpretation h3)
  ≡
  OS.hamiltonian
    (H2OS.asOSReconstructionAuthority
      (H2.reconstruction h2) group)
h3PhysicalHamiltonianIsExactH2Reconstruction h3 = Agda.Builtin.Equality.refl

cmp119RealSameHCompilerLevel : ProofLevel
cmp119RealSameHCompilerLevel = machineChecked

-- This is now the genuine H3 source theorem and nothing more:
-- no-positive-subgap semantics of the R281 covariance spectrum are the spectral
-- separation semantics of H2's exact reconstructed Hamiltonian.
cmp119RealSameHPhysicalSpectrumLevel : ProofLevel
cmp119RealSameHPhysicalSpectrumLevel = conditional
