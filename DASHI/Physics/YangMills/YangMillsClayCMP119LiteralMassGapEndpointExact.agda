{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119LiteralMassGapEndpointExact where

------------------------------------------------------------------------
-- MASS-GAP ENDPOINT ON THE SOURCE-CONSTRUCTED LITERAL Y.
--
-- For each literal group:
--   H5 gives the exact real selected H1/H2/H3 package;
--   H3 constructs the physical mass-gap certificate;
--   Y.hamiltonian and Y.massGap are definitionally those exact coordinates.
--
-- Remaining fields only interpret that constructed certificate in the opaque
-- literal Clay semantic predicates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2Exact as H2
import DASHI.Physics.YangMills.YangMillsClayCMP119CompactSimplePhysicalH5Exact as H5
import DASHI.Physics.YangMills.YangMillsClayCMP119LiteralConstructionFromH5Exact as Literal
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSameOSH3Exact as H3
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedGapExact as RealGap
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

physicalCertificateForGroup :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws}
    (h5 :
      H5.CMP119CompactSimplePhysicalH5
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws)
    group →
  OS.PhysicalMassGapCertificate Hamiltonian ℚ
physicalCertificateForGroup h5 group =
  let
    package = H5.physicalPackageForLiteralGroup h5 group
  in
  H3.physicalMassGapCertificate
    (H5.sameOSH3 package)
    (H5.positiveGapCandidate package)

record CMP119LiteralMassGapSemantics
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
    (h5 :
      H5.CMP119CompactSimplePhysicalH5
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws)
    (local :
      Literal.CMP119LiteralLocalCoordinates
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5)
    : Set₂ where
  private
    Y = Literal.literalConstruction local

  field
    certificateMeansVacuumSector :
      ∀ group →
      (certificate : OS.PhysicalMassGapCertificate Hamiltonian ℚ) →
      OS.hamiltonian certificate ≡ Top.hamiltonian Y group →
      OS.gap certificate ≡ Top.massGap Y group →
      Top.IsVacuumSectorAndPositiveEnergyComplement S
        (Top.hilbertSpace Y group)
        (Top.hamiltonian Y group)
        (Top.vacuum Y group)

    certificateMeansStrictPositiveFiniteGap :
      ∀ group →
      (certificate : OS.PhysicalMassGapCertificate Hamiltonian ℚ) →
      OS.hamiltonian certificate ≡ Top.hamiltonian Y group →
      OS.gap certificate ≡ Top.massGap Y group →
      Top.IsStrictlyPositiveFiniteMassGap S
        (Top.hamiltonian Y group)
        (Top.massGap Y group)

    certificateMeansPhysicalScaleLowerBound :
      ∀ group →
      (certificate : OS.PhysicalMassGapCertificate Hamiltonian ℚ) →
      OS.gap certificate ≡ Top.massGap Y group →
      Top.PhysicalScaleLowerBoundUniform S group
        (Top.massGap Y group)

    certificateMeansNoSubgapPollution :
      ∀ group →
      (certificate : OS.PhysicalMassGapCertificate Hamiltonian ℚ) →
      OS.hamiltonian certificate ≡ Top.hamiltonian Y group →
      OS.gap certificate ≡ Top.massGap Y group →
      Top.NoSpectralPollutionBelowGap S group
        (Top.hamiltonian Y group)
        (Top.massGap Y group)

    transferGapCoreMeansDerivedNotAssumed :
      ∀ group →
      let package = H5.physicalPackageForLiteralGroup h5 group in
      Gap.PositiveTransferGapCore
        (R281.asReconstructedClusteringSpectrum
          (RealGap.spectrumSource (H5.realSelected package))) →
      Top.GapAndClusteringAreDerivedNotAssumed S group

open CMP119LiteralMassGapSemantics public

certificateHamiltonianIsLiteral :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws h5}
    (local :
      Literal.CMP119LiteralLocalCoordinates
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5)
    group →
  OS.hamiltonian (physicalCertificateForGroup h5 group)
  ≡ Top.hamiltonian (Literal.literalConstruction local) group
certificateHamiltonianIsLiteral local group = refl

certificateGapIsLiteral :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws h5}
    (local :
      Literal.CMP119LiteralLocalCoordinates
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5)
    group →
  OS.gap (physicalCertificateForGroup h5 group)
  ≡ Top.massGap (Literal.literalConstruction local) group
certificateGapIsLiteral local group = refl

literalMassGap :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws h5}
    {local :
      Literal.CMP119LiteralLocalCoordinates
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5} →
  CMP119LiteralMassGapSemantics
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    LieElement GroupElement
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S h2 covarianceLaws h5 local →
  Five.CutoffUniformPhysicalMassGap
    (Literal.literalConstruction local)
literalMassGap
    {h5 = h5} {local = local}
    semantics = record
  { Five.CutoffUniformPhysicalMassGap.vacuumSectorAndPositiveEnergyComplement =
      λ group →
        certificateMeansVacuumSector semantics group
          (physicalCertificateForGroup h5 group)
          (certificateHamiltonianIsLiteral local group)
          (certificateGapIsLiteral local group)
  ; Five.CutoffUniformPhysicalMassGap.strictlyPositiveFiniteMassGap =
      λ group →
        certificateMeansStrictPositiveFiniteGap semantics group
          (physicalCertificateForGroup h5 group)
          (certificateHamiltonianIsLiteral local group)
          (certificateGapIsLiteral local group)
  ; Five.CutoffUniformPhysicalMassGap.physicalScaleLowerBoundUniform =
      λ group →
        certificateMeansPhysicalScaleLowerBound semantics group
          (physicalCertificateForGroup h5 group)
          (certificateGapIsLiteral local group)
  ; Five.CutoffUniformPhysicalMassGap.noSpectralPollutionBelowGap =
      λ group →
        certificateMeansNoSubgapPollution semantics group
          (physicalCertificateForGroup h5 group)
          (certificateHamiltonianIsLiteral local group)
          (certificateGapIsLiteral local group)
  ; Five.CutoffUniformPhysicalMassGap.gapAndClusteringDerived =
      λ group →
        let package = H5.physicalPackageForLiteralGroup h5 group
        in
        transferGapCoreMeansDerivedNotAssumed semantics group
          (RealGap.positiveTransferGapCore
            (H5.realSelected package)
            (H5.positiveGapCandidate package))
  }

cmp119LiteralMassGapEndpointCompilerLevel : ProofLevel
cmp119LiteralMassGapEndpointCompilerLevel = machineChecked

cmp119LiteralMassGapSemanticInterpretationLevel : ProofLevel
cmp119LiteralMassGapSemanticInterpretationLevel = conditional
