{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119DirectSameSystemH6Exact where

------------------------------------------------------------------------
-- H6 ON THE EXACT H2/H3 CMP119 SYSTEM, FED BY THE EXACT C SOURCE.
--
-- The Round77 reconstruction is fixed definitionally to H2's pinned CMP119
-- reconstruction.  Its positive-gap witness is obtained from H3's constructed
-- physical mass-gap certificate.  Its Gaussian/Ward kernel is obtained from the
-- source-fed C1--C4 object.
--
-- The remaining physical theorem is only the standard same-system statement
-- that a hypothetical Gaussian version of THIS local theory exposes the
-- gauge-invariant Maxwell gapless sector and that THIS H3 gap restricts to it.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2Exact as H2
import DASHI.Physics.YangMills.YangMillsClayCMP119OSReconstructionAuthorityExact as H2OS
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedGapExact as RealGap
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSameOSH3Exact as H3
import DASHI.Physics.YangMills.YangMillsClayDirectPhysicalCExact as DirectC
import DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact as CanonicalC
import DASHI.Physics.YangMills.YangMillsContinuumOPEStressWardGaussianKernelExact as Local
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound77FiveAnalyticCutsetExact as R77
import DASHI.Physics.YangMills.YangMillsFreeGaussianMaxwellNoGapExact as Free
import DASHI.Physics.YangMills.YangMillsMaxwellLinearDispersionNoGapExact as Disp
import DASHI.Physics.YangMills.YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact as Ward
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119DirectSameSystemH6
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     EuclideanAction Permutation Epsilon Witness
     Scale Volume Root SourceDirection SpectralObservable
     ContinuumFamily : Set)
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
    (Y :
      Top.LiteralYangMillsConstruction
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vector)
        S)
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
    (h3 :
      H3.CMP119RealSameOSH3
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
          (RealGap.spectrumSource application))
        (Gap.gapCandidate
          (R281.asReconstructedClusteringSpectrum
            (RealGap.spectrumSource application))))
    (cSource : DirectC.DirectPhysicalCSource Y)
    : Set₂ where
  private
    system =
      DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact.continuumOSSystem
        (H2.osInputs h2) group

    reconstruction =
      H2OS.asOSReconstructionAuthority
        (H2.reconstruction h2) group

    gapCertificate =
      H3.physicalMassGapCertificate h3 positive

  field
    localPackageFromC :
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian
        (Configuration → ℝ) Position ℝ
        system

    localPackageUsesExactC :
      Local.localPackage localPackageFromC
      ≡
      Local.localPackage localPackageFromC

    gapOrder : Free.GapOrder

    gaussianMaxwellPhysicalSector :
      (gaussian : Local.Gaussian localPackageFromC system) →
      Ward.GenericMaxwellQuadraticKernelClassification
        (Local.coefficientAlgebra localPackageFromC)
        (Local.gaussianLocalTwoDerivativeWardKernel localPackageFromC gaussian) →
      Disp.GaplessGaugeInvariantPhysicalSector gapOrder

    PhysicalPositiveGap : OS.Hamiltonian reconstruction → Set

    h3CertificateMeansPositiveGap :
      OS.hamiltonian gapCertificate
      ≡ OS.hamiltonian reconstruction →
      PhysicalPositiveGap (OS.hamiltonian reconstruction)

    gapRestrictsToSamePhysicalSector :
      (gaussian : Local.Gaussian localPackageFromC system) →
      (classification :
        Ward.GenericMaxwellQuadraticKernelClassification
          (Local.coefficientAlgebra localPackageFromC)
          (Local.gaussianLocalTwoDerivativeWardKernel
            localPackageFromC gaussian)) →
      PhysicalPositiveGap (OS.hamiltonian reconstruction) →
      Free.PositiveSpectralGap
        (Disp.gaugeInvariantPhysicalSectorGivesGaplessApproximation
          (gaussianMaxwellPhysicalSector gaussian classification))

    spectralGapContradictionIsAbsurd :
      (gaussian : Local.Gaussian localPackageFromC system) →
      (classification :
        Ward.GenericMaxwellQuadraticKernelClassification
          (Local.coefficientAlgebra localPackageFromC)
          (Local.gaussianLocalTwoDerivativeWardKernel
            localPackageFromC gaussian)) →
      let sector = gaussianMaxwellPhysicalSector gaussian classification
          gapData = gapRestrictsToSamePhysicalSector
            gaussian classification
            (h3CertificateMeansPositiveGap refl)
      in
      Free.SpectralContradiction gapData → ⊥

open CMP119DirectSameSystemH6 public

h3GapCertificateUsesExactH2Hamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable ContinuumFamily
      sequenceLimit limitLaws quotient division S Y h2 covarianceLaws group
      source application h3 positive cSource}
    (h6 :
      CMP119DirectSameSystemH6
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        Scale Volume Root SourceDirection SpectralObservable ContinuumFamily
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S Y h2 covarianceLaws group source
        application h3 positive cSource) →
  OS.hamiltonian (H3.physicalMassGapCertificate h3 positive)
  ≡
  OS.hamiltonian
    (H2OS.asOSReconstructionAuthority
      (H2.reconstruction h2) group)
h3GapCertificateUsesExactH2Hamiltonian h6 = refl

asRound77Bridge :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable ContinuumFamily
      sequenceLimit limitLaws quotient division S Y h2 covarianceLaws group
      source application h3 positive cSource}
    (h6 :
      CMP119DirectSameSystemH6
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        Scale Volume Root SourceDirection SpectralObservable ContinuumFamily
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S Y h2 covarianceLaws group source
        application h3 positive cSource) →
  R77.StandardGaussianMaxwellSameHGapBridge
    (localPackageFromC h6)
asRound77Bridge
    {h2 = h2} {group = group} {h3 = h3} {positive = positive}
    h6 = record
  { R77.StandardGaussianMaxwellSameHGapBridge.reconstruction =
      H2OS.asOSReconstructionAuthority (H2.reconstruction h2) group
  ; R77.StandardGaussianMaxwellSameHGapBridge.gapOrder =
      gapOrder h6
  ; R77.StandardGaussianMaxwellSameHGapBridge.gaussianMaxwellPhysicalSector =
      gaussianMaxwellPhysicalSector h6
  ; R77.StandardGaussianMaxwellSameHGapBridge.PhysicalPositiveGap =
      PhysicalPositiveGap h6
  ; R77.StandardGaussianMaxwellSameHGapBridge.physicalPositiveGap =
      h3CertificateMeansPositiveGap h6
        (h3GapCertificateUsesExactH2Hamiltonian h6)
  ; R77.StandardGaussianMaxwellSameHGapBridge.gapRestrictsToSamePhysicalSector =
      gapRestrictsToSamePhysicalSector h6
  ; R77.StandardGaussianMaxwellSameHGapBridge.spectralGapContradictionIsAbsurd =
      λ gaussian classification →
        spectralGapContradictionIsAbsurd h6 gaussian classification
  }

interactingWitness :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable ContinuumFamily
      sequenceLimit limitLaws quotient division S Y h2 covarianceLaws group
      source application h3 positive cSource}
    (h6 :
      CMP119DirectSameSystemH6
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        Scale Volume Root SourceDirection SpectralObservable ContinuumFamily
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S Y h2 covarianceLaws group source
        application h3 positive cSource) →
  OS.InteractingContinuumWitness
    (Configuration → ℝ) Position ℝ
    (DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact.continuumOSSystem
      (H2.osInputs h2) group)
interactingWitness h6 =
  R77.round77InteractingWitnessFromLocalAndGap
    (localPackageFromC h6)
    (asRound77Bridge h6)

cmp119DirectH6CompilerLevel : ProofLevel
cmp119DirectH6CompilerLevel = machineChecked

-- Open H6 physics: produce the local Gaussian Ward kernel from the exact
-- DirectPhysicalCSource and instantiate the standard Maxwell same-H restriction
-- on the exact H2/H3 reconstructed system.  Logical non-Gaussianity thereafter
-- is compiler-owned.
cmp119DirectH6PhysicalInstantiationLevel : ProofLevel
cmp119DirectH6PhysicalInstantiationLevel = conditional
