{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119CompactSimplePhysicalH5Exact where

------------------------------------------------------------------------
-- H5 ON THE ACTUAL CMP119 / REAL-COVARIANCE CONSTRUCTION.
--
-- Classification is compiler-owned.  The one physical continuation theorem
-- must, for arbitrary classified compact-simple G and its quantitative package,
-- construct the SAME:
--
--   * group-parametric selected-background/five-block source;
--   * real CMP119 selected CMP116/spectral application;
--   * exact H2-OS / H3 reconstructed-H spectral interpretation.
--
-- Thus "all G" is not an endpoint quantifier over unrelated witnesses.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage as Compact
import DASHI.Physics.YangMills.YangMillsCompactSimpleParametricPromotionReductionExact as Groups
import DASHI.Physics.YangMills.BalabanGroupParametricFiveBlockSignedG2Exact as FiveBlock
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2Exact as H2
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedGapExact as RealGap
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedWilsonH2Exact as H2Wilson
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSameOSH3Exact as H3
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119GroupPhysicalPackage
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     EuclideanAction Permutation Epsilon Witness
     LieElement GroupElement : Set)
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
      H2.CMP119DirectPhysicalH2
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : G)
    (classifiedGroup : Compact.CompactSimpleLieGroup)
    (quantitative :
      Compact.QuantitativeCompactLiePackage
        ℚ LieElement GroupElement classifiedGroup)
    : Set₂ where
  field
    fiveBlock :
      FiveBlock.GroupParametricFiveBlockG2Data
        LieElement GroupElement classifiedGroup

    fiveBlockUsesQuantitativePackage :
      FiveBlock.quantitativeLiePackage fiveBlock ≡ quantitative

    SourceScale SourceVolume SourceRoot SourceDirection' SpectralObservable' : Set

    publishedCMP116 :
      CMP116.PublishedCMP116DifferentiatedLocalization
        SourceScale SourceVolume SourceRoot SourceDirection' ℝ

    realSelected :
      RealGap.CMP119RealSelectedSpectrumApplication
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector
        SourceScale SourceVolume SourceRoot SourceDirection'
        SpectralObservable' ℚ
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        (H2.osInputs h2)
        covarianceLaws
        group
        publishedCMP116

    Loop : Set

    selectedWilson :
      H2Wilson.CMP119RealSelectedWilsonPresentation
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector Loop
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        (H2.osInputs h2)
        covarianceLaws
        group
        (RealGap.tests realSelected)

    positiveGapCandidate :
      Gap.PositiveEnergy
        (R281.asReconstructedClusteringSpectrum
          (RealGap.spectrumSource realSelected))
        (Gap.gapCandidate
          (R281.asReconstructedClusteringSpectrum
            (RealGap.spectrumSource realSelected)))

    sameOSH3 :
      H3.CMP119RealSameOSH3
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        SourceScale SourceVolume SourceRoot SourceDirection'
        SpectralObservable'
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S
        h2 covarianceLaws group publishedCMP116 realSelected

open CMP119GroupPhysicalPackage public

record CMP119CompactSimplePhysicalH5
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     EuclideanAction Permutation Epsilon Witness
     LieElement GroupElement : Set)
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
      H2.CMP119DirectPhysicalH2
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    : Set₂ where
  field
    authority :
      Compact.CompactSimpleQuantitativeAuthority
        ℚ LieElement GroupElement

    literalToClassified :
      G → Compact.CompactSimpleLieGroup

    continuePhysicalPackage :
      (group : G) →
      (quantitative :
        Compact.QuantitativeCompactLiePackage
          ℚ LieElement GroupElement (literalToClassified group)) →
      CMP119GroupPhysicalPackage
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S
        h2 covarianceLaws
        group
        (literalToClassified group)
        quantitative

open CMP119CompactSimplePhysicalH5 public

physicalPackageForLiteralGroup :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws}
    (h5 :
      CMP119CompactSimplePhysicalH5
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws)
    group →
  CMP119GroupPhysicalPackage
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    LieElement GroupElement
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S h2 covarianceLaws
    group
    (literalToClassified h5 group)
    (Compact.compactSimpleHasQuantitativePackage
      (authority h5) (literalToClassified h5 group))
physicalPackageForLiteralGroup h5 group =
  continuePhysicalPackage h5 group
    (Compact.compactSimpleHasQuantitativePackage
      (authority h5) (literalToClassified h5 group))

cmp119H5ClassificationCompilerLevel : ProofLevel
cmp119H5ClassificationCompilerLevel =
  Groups.compactSimpleClassificationToParametricFamilyLevel

-- One genuine H5 theorem remains: continuePhysicalPackage.  It must build the
-- five-block and exact real H1/H3 package from the quantitative Lie data for
-- arbitrary classified G; classification/package lookup itself is compiled.
cmp119H5PhysicalContinuationLevel : ProofLevel
cmp119H5PhysicalContinuationLevel = conditional
