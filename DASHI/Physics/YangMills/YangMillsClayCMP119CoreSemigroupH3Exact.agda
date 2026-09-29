{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119CoreSemigroupH3Exact where

------------------------------------------------------------------------
-- H3 ON THE ACTUAL PRE-GAP CMP119 RECONSTRUCTED HAMILTONIAN.
--
-- The R281 correlation is definitionally the continuum CMP119 covariance,
-- but that fact ALONE does not identify it with a transfer-semigroup matrix
-- element or establish cyclicity of selected Wilson vectors.  Those are
-- genuinely physical input theorems here.
--
-- The source also provides physical spectral completeness: every positive
-- subgap physical spectral state must have a detected R281 subgap mode.  Once
-- that map exists, the existing R281/GAP fast/slow contradiction excludes the
-- physical subgap and yields the SAME-core-H spectral certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Data.Product using (_×_; _,_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2CoreExact as H2
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSameOSH3Exact as LegacyH3
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as CoreOS
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedGapExact as RealGap
import DASHI.Physics.YangMills.YangMillsClayCMP119OSReconstructionAuthorityExact as H2OS
import DASHI.Physics.YangMills.BalabanOSIndexedTransferCoordinateRound331Exact as R331
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact as R302
import DASHI.Physics.YangMills.BalabanPairwiseMassRateFromTransferCoordinateRound311Exact as R311
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119CoreSemigroupH3
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
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vector))
    (h2 :
      H2.CMP119DirectPhysicalH2Core
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
      RealGap.CMP119CoreRealSelectedSpectrumApplication
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector
        Scale Volume Root SourceDirection SpectralObservable ℚ
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        (H2.coreInputs h2) covarianceLaws group source)
    : Set₂ where
  private
    spectrum =
      R281.asReconstructedClusteringSpectrum
        (RealGap.spectrumSourceCore application)

    hCore =
      Pinned.reconstructedHamiltonianCore
        (H2.reconstructionCore h2) group

  field
    -- The transfer coordinate is indexed by the SAME H2-core OS
    -- reconstruction.  Its semigroup interpretation is physical data,
    -- not a chosen second Hamiltonian.
    indexedTransfer :
      R331.PreGapOSIndexedTransferCoordinate
        (H2OS.asPreGapOSReconstructionAuthority
          (H2.reconstructionCore h2) group) ℚ

    -- The exact R281 candidate is the energy corresponding to the selected
    -- physical transfer decay ratio.  This is not implied by their types.
    selectedGapIsTransferCandidate :
      Gap.gapCandidate spectrum ≡
      R302.candidateEnergy (R331.coordinateCore indexedTransfer)

    -- Selected positive-time Wilson vectors are in the physical Hilbert
    -- space produced by H2 core (not in an auxiliary transfer space).
    wilsonVector : SpectralObservable → Vector

    -- This operation must really be the H2-core transfer semigroup matrix
    -- element, e.g. <psi,e^{-t H_core} psi> with vacuum subtraction.
    ConnectedSemigroupMatrixElement :
      Hamiltonian → Vector → Nat → ℝ

    exactSelectedCovarianceIsCoreSemigroup :
      ∀ observable time →
      Gap.connectedCorrelation spectrum observable time
      ≡
      ConnectedSemigroupMatrixElement
        hCore (wilsonVector observable) time

    PhysicalPositiveSubgapMode : ℚ → Set

    -- Cyclic/determining-class payment, not an automatic property of merely
    -- selecting some Wilson observables.  It must be obtained from physical
    -- sector cyclicity, positivity and nonzero selected overlap.
    everyPhysicalSubgapDetected :
      ∀ energy →
      PhysicalPositiveSubgapMode energy →
      Gap.SubgapMode spectrum energy

    SpectrumAboveVacuumGap : Hamiltonian → ℚ → Set

    -- The applicable spectral theorem on the physical H2 Hilbert space.
    -- This must not be justified by an auxiliary RG gap.
    physicalSpectrumCompleteness :
      (∀ energy →
        Gap.PositiveEnergy spectrum energy →
        Gap.StrictlyBelow spectrum energy (Gap.gapCandidate spectrum) →
        PhysicalPositiveSubgapMode energy →
        Gap.Empty) →
      SpectrumAboveVacuumGap hCore (Gap.gapCandidate spectrum)

open CMP119CoreSemigroupH3 public

physicalCorePositiveSubgapExcluded :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable
      sequenceLimit limitLaws quotient division S
      h2 covarianceLaws group source application} →
  (physical :
    CMP119CoreSemigroupH3
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable
      {sequenceLimit = sequenceLimit}
      limitLaws quotient division S
      h2 covarianceLaws group source application) →
  (positive :
    Gap.PositiveEnergy
      (R281.asReconstructedClusteringSpectrum
        (RealGap.spectrumSourceCore application))
      (Gap.gapCandidate
        (R281.asReconstructedClusteringSpectrum
          (RealGap.spectrumSourceCore application)))) →
  ∀ energy →
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum
      (RealGap.spectrumSourceCore application)) energy →
  Gap.StrictlyBelow
    (R281.asReconstructedClusteringSpectrum
      (RealGap.spectrumSourceCore application))
    energy
    (Gap.gapCandidate
      (R281.asReconstructedClusteringSpectrum
        (RealGap.spectrumSourceCore application))) →
  PhysicalPositiveSubgapMode physical energy →
  Gap.Empty
physicalCorePositiveSubgapExcluded
    {application = application} physical positive energy positiveEnergy below mode =
  let
    gapCore = RealGap.positiveCoreTransferGapCore application positive
  in
  Gap.noPositiveSubgapMode gapCore
    energy positiveEnergy below
    (everyPhysicalSubgapDetected physical energy mode)

physicalCoreSpectrumGap :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable
      sequenceLimit limitLaws quotient division S
      h2 covarianceLaws group source application}
    (physical :
      CMP119CoreSemigroupH3
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        Scale Volume Root SourceDirection SpectralObservable
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S
        h2 covarianceLaws group source application)
    (positive :
      Gap.PositiveEnergy
        (R281.asReconstructedClusteringSpectrum
          (RealGap.spectrumSourceCore application))
        (Gap.gapCandidate
          (R281.asReconstructedClusteringSpectrum
            (RealGap.spectrumSourceCore application)))) →
  SpectrumAboveVacuumGap physical
    (Pinned.reconstructedHamiltonianCore
      (H2.reconstructionCore h2) group)
    (Gap.gapCandidate
      (R281.asReconstructedClusteringSpectrum
        (RealGap.spectrumSourceCore application)))
physicalCoreSpectrumGap physical positive =
  physicalSpectrumCompleteness physical
    (physicalCorePositiveSubgapExcluded physical positive)

physicalCoreMassGapCertificate :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable
      sequenceLimit limitLaws quotient division S
      h2 covarianceLaws group source application}
    (physical :
      CMP119CoreSemigroupH3
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        Scale Volume Root SourceDirection SpectralObservable
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S
        h2 covarianceLaws group source application)
    (positive :
      Gap.PositiveEnergy
        (R281.asReconstructedClusteringSpectrum
          (RealGap.spectrumSourceCore application))
        (Gap.gapCandidate
          (R281.asReconstructedClusteringSpectrum
            (RealGap.spectrumSourceCore application)))) →
  OS.PhysicalMassGapCertificate Hamiltonian ℚ
physicalCoreMassGapCertificate
    {h2 = h2} {group = group} {application = application} physical positive =
  record
    { OS.PhysicalMassGapCertificate.hamiltonian =
        Pinned.reconstructedHamiltonianCore
          (H2.reconstructionCore h2) group
    ; OS.PhysicalMassGapCertificate.gap =
        Gap.gapCandidate
          (R281.asReconstructedClusteringSpectrum
            (RealGap.spectrumSourceCore application))
    ; OS.PhysicalMassGapCertificate.Positive =
        Gap.PositiveEnergy
          (R281.asReconstructedClusteringSpectrum
            (RealGap.spectrumSourceCore application))
    ; OS.PhysicalMassGapCertificate.gapPositive = positive
    ; OS.PhysicalMassGapCertificate.SpectrumAboveVacuumGap =
        SpectrumAboveVacuumGap physical
          (Pinned.reconstructedHamiltonianCore
            (H2.reconstructionCore h2) group)
          (Gap.gapCandidate
            (R281.asReconstructedClusteringSpectrum
              (RealGap.spectrumSourceCore application)))
    ; OS.PhysicalMassGapCertificate.spectrumAboveVacuumGap =
        physicalCoreSpectrumGap physical positive
    }

------------------------------------------------------------------------
-- R331/R311 transport is the exact same core Hamiltonian, by construction.
-- The candidate-energy calibration is the named physical equality already
-- stored in CMP119CoreSemigroupH3.
------------------------------------------------------------------------

coreTransferHamiltonianIsH2Reconstruction :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable
      sequenceLimit limitLaws quotient division S
      h2 covarianceLaws group source application}
    (physical :
      CMP119CoreSemigroupH3
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        Scale Volume Root SourceDirection SpectralObservable
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S
        h2 covarianceLaws group source application) →
  R311.reconstructedHamiltonian
    (R331.preGapAsSameHamiltonianTransferCoordinate
      (H2OS.asPreGapOSReconstructionAuthority
        (H2.reconstructionCore h2) group)
      (indexedTransfer physical))
  ≡
  Pinned.reconstructedHamiltonianCore
    (H2.reconstructionCore h2) group
coreTransferHamiltonianIsH2Reconstruction physical = refl

------------------------------------------------------------------------
-- Compatibility theorem: after OS4 is attached, the old H3 record consumes
-- precisely this semigroup/overlap/completeness source.  Its spectrum predicate
-- is NOT trivial: it states equality to the core Hamiltonian AND equality of
-- every selected R281 correlation with the core-H semigroup matrix element.
------------------------------------------------------------------------

coreH3AsLegacy :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable
      sequenceLimit limitLaws quotient division S}
    (h2 :
      H2.CMP119DirectPhysicalH2Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (clustering : H2.CMP119DirectPhysicalH2OS4Attachment h2)
    {covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit}
    {group : G}
    {source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ}
    {application :
      RealGap.CMP119CoreRealSelectedSpectrumApplication
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector
        Scale Volume Root SourceDirection SpectralObservable ℚ
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        (H2.coreInputs h2) covarianceLaws group source} →
  CMP119CoreSemigroupH3
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    Scale Volume Root SourceDirection SpectralObservable
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
    h2 covarianceLaws group source application →
  LegacyH3.CMP119RealSameOSH3
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    Scale Volume Root SourceDirection SpectralObservable
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
    (H2.asLegacyH2 h2 clustering)
    covarianceLaws group source
    (RealGap.coreSelectedAsLegacy
      (H2.coreInputs h2)
      (H2.asPinnedOS4Attachment clustering)
      application)
coreH3AsLegacy h2 clustering {group = group} {application = application} physical = record
  { LegacyH3.CMP119RealSameOSH3.SpectrumOfH2ReconstructedHamiltonian =
      λ h spectrum →
        (h ≡ Pinned.reconstructedHamiltonianCore
          (H2.reconstructionCore h2) group)
        ×
        (∀ observable time →
          Gap.connectedCorrelation spectrum observable time
          ≡
          ConnectedSemigroupMatrixElement physical
            (Pinned.reconstructedHamiltonianCore
              (H2.reconstructionCore h2) group)
            (wilsonVector physical observable) time)
  ; LegacyH3.CMP119RealSameOSH3.exactSelectedR281SpectrumIsH2Reconstructed =
      refl , exactSelectedCovarianceIsCoreSemigroup physical
  ; LegacyH3.CMP119RealSameOSH3.SpectrumAboveVacuumGap =
      SpectrumAboveVacuumGap physical
  ; LegacyH3.CMP119RealSameOSH3.noPositiveSubgapMeansActualSpectrumSeparated =
      λ noSubgap →
        physicalSpectrumCompleteness physical
          (λ energy positive below mode →
            noSubgap energy positive below
              (everyPhysicalSubgapDetected physical energy mode))
  }

coreH3ToLegacyAfterOS4CompilerLevel : ProofLevel
coreH3ToLegacyAfterOS4CompilerLevel = machineChecked

cmp119CoreH3SpectralExclusionCompilerLevel : ProofLevel
cmp119CoreH3SpectralExclusionCompilerLevel = machineChecked

-- Unproved physics: selected Wilson/semigroup identity, positivity and
-- nonzero overlap/cyclicity, physical-sector spectrum completeness.
cmp119CoreH3SemigroupAndCyclicityLevel : ProofLevel
cmp119CoreH3SemigroupAndCyclicityLevel = conditional
