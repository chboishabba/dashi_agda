{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119LiteralConstructionFromH5Exact where

------------------------------------------------------------------------
-- LITERAL Y WITH MASS GAP CHOSEN FROM THE EXACT H5/R281 PACKAGE.
--
-- H2 already fixes finite/continuum/Schwinger/Hilbert/Hamiltonian/vacuum.
-- H5 fixes, for every literal group, one real selected R281 spectrum with a
-- positive rational gapCandidate.  Therefore Y.massGap should be that exact
-- coordinate by construction, not an independently selected rational.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2Exact as H2
import DASHI.Physics.YangMills.YangMillsClayCMP119CompactSimplePhysicalH5Exact as H5
import DASHI.Physics.YangMills.YangMillsClayCMP119LiteralConstructionCoreExact as Core
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedGapExact as RealGap
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119LiteralLocalCoordinates
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
    : Set₁ where
  field
    spacetime : X
    localObservable : G → Position → Configuration → ℝ
    curvatureOperator : G → CurvaturePolynomial → LocalOperator
    opeCoefficient :
      G → LocalOperator → LocalOperator → LocalOperator →
      Position → OPECoefficient
    opeRemainder :
      G → LocalOperator → LocalOperator → Position → Nat → ℚ
    stressTensor : G → StressTensor

open CMP119LiteralLocalCoordinates public

massGapFromH5 :
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
  ℚ
massGapFromH5 h5 group =
  let package = H5.physicalPackageForLiteralGroup h5 group
  in
  Gap.gapCandidate
    (R281.asReconstructedClusteringSpectrum
      (RealGap.spectrumSource (H5.realSelected package)))

asCoreFields :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws h5}
    (local :
      CMP119LiteralLocalCoordinates
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5) →
  Core.CMP119LiteralConstructionFields
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S h2
asCoreFields {h5 = h5} local = record
  { Core.CMP119LiteralConstructionFields.spacetime =
      spacetime local
  ; Core.CMP119LiteralConstructionFields.localObservable =
      localObservable local
  ; Core.CMP119LiteralConstructionFields.curvatureOperator =
      curvatureOperator local
  ; Core.CMP119LiteralConstructionFields.opeCoefficient =
      opeCoefficient local
  ; Core.CMP119LiteralConstructionFields.opeRemainder =
      opeRemainder local
  ; Core.CMP119LiteralConstructionFields.stressTensor =
      stressTensor local
  ; Core.CMP119LiteralConstructionFields.massGap =
      massGapFromH5 h5
  }

literalConstruction :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws h5} →
  CMP119LiteralLocalCoordinates
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    LieElement GroupElement
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S h2 covarianceLaws h5 →
  Top.LiteralYangMillsConstruction
    (Physical.physicalLiteralCarriers
      G X Nat Configuration ℝ
      (Configuration → ℝ) Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      Hilbert Hamiltonian Vector)
    S
literalConstruction local =
  Core.literalConstruction (asCoreFields local)

literalMassGapIsExactH5GapCandidate :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws h5}
    (local :
      CMP119LiteralLocalCoordinates
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5)
    group →
  Top.massGap (literalConstruction local) group
  ≡ massGapFromH5 h5 group
literalMassGapIsExactH5GapCandidate local group = refl

cmp119LiteralConstructionFromH5Level : ProofLevel
cmp119LiteralConstructionFromH5Level = machineChecked
