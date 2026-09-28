{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalEndpointExact where

------------------------------------------------------------------------
-- DIRECT PHYSICAL CMP119 -> LITERAL CLAY ENDPOINT.
--
-- This endpoint does not accept abstract finite/continuum/gap/local/nontrivial
-- theorem packages.  It compiles them from the concrete source stack:
--
--   H2 canonical CMP119 completion/reconstruction
--   H5 per-group quantitative real selected H1/H2b/H3 package
--   source-constructed literal Y
--   source-fed C1--C4
--   H3 certificate semantics
--   exact-system H6 Round77 semantics
--
-- Only structural endpoint interpretation (compact-simple/4D/parameterization)
-- remains outside those source objects.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2Exact as H2
import DASHI.Physics.YangMills.YangMillsClayCMP119CompactSimplePhysicalH5Exact as H5
import DASHI.Physics.YangMills.YangMillsClayCMP119LiteralConstructionFromH5Exact as Literal
import DASHI.Physics.YangMills.YangMillsClayCMP119LiteralH2EndpointExact as H2Endpoint
import DASHI.Physics.YangMills.YangMillsClayDirectPhysicalCExact as DirectC
import DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact as CanonicalC
import DASHI.Physics.YangMills.YangMillsClayCMP119LiteralMassGapEndpointExact as GapEndpoint
import DASHI.Physics.YangMills.YangMillsClayCMP119LiteralH6EndpointExact as H6Endpoint
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119DirectPhysicalEndpoint
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     EuclideanAction Permutation Epsilon Witness
     LieElement GroupElement ContinuumFamily : Set)
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
    fourDimensionalEuclidean :
      Top.IsFourDimensionalEuclidean S (Top.spacetime Y)

    cSource :
      DirectC.DirectPhysicalCSource Y

    massGapSemantics :
      GapEndpoint.CMP119LiteralMassGapSemantics
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5 local

    h6Semantics :
      H6Endpoint.CMP119LiteralH6Semantics
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement ContinuumFamily
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5 local cSource

open CMP119DirectPhysicalEndpoint public

structural :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      ContinuumFamily sequenceLimit limitLaws quotient division S h2
      covarianceLaws h5 local}
    (source :
      CMP119DirectPhysicalEndpoint
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement ContinuumFamily
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5 local) →
  Five.LiteralClayStructuralBase
    (Literal.literalConstruction local)
structural source = record
  { Five.LiteralClayStructuralBase.compactSimple =
      H5.literalCompactSimple h5
  ; Five.LiteralClayStructuralBase.fourDimensionalEuclidean =
      fourDimensionalEuclidean source
  ; Five.LiteralClayStructuralBase.compactSimpleParameterization =
      H5.literalCompactSimpleParameterizationPreserved h5
  }

localQFT :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      ContinuumFamily sequenceLimit limitLaws quotient division S h2
      covarianceLaws h5 local}
    (source :
      CMP119DirectPhysicalEndpoint
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement ContinuumFamily
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5 local) →
  Five.ContinuumLocalFieldOPEStressWard
    (Literal.literalConstruction local)
localQFT source =
  CanonicalC.asContinuumLocalFieldOPEStressWard
    (DirectC.asGoal1CanonicalCSource (cSource source))

literalEvidence :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      ContinuumFamily sequenceLimit limitLaws quotient division S h2
      covarianceLaws h5 local}
    (source :
      CMP119DirectPhysicalEndpoint
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement ContinuumFamily
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5 local) →
  Top.LiteralClayEvidence
    (Literal.literalConstruction local)
literalEvidence
    {local = local}
    source =
  Five.literalClayEvidenceFromFiveTheorems
    (Literal.literalConstruction local)
    (structural source)
    (H2Endpoint.literalFiniteRG local)
    (GapEndpoint.literalMassGap
      (massGapSemantics source))
    (H2Endpoint.literalContinuum local)
    (localQFT source)
    (H6Endpoint.literalNontriviality
      (h6Semantics source))

literalSolution :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      ContinuumFamily sequenceLimit limitLaws quotient division S h2
      covarianceLaws h5 local}
    (source :
      CMP119DirectPhysicalEndpoint
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement ContinuumFamily
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws h5 local) →
  Clay.ClayYangMillsSolution
    (Top.literalClayVocabulary
      (Literal.literalConstruction local))
literalSolution {local = local} source =
  Top.literalTopDownClaySolution
    (Literal.literalConstruction local)
    (literalEvidence source)

cmp119DirectPhysicalEndpointCompilerLevel : ProofLevel
cmp119DirectPhysicalEndpointCompilerLevel = machineChecked

-- This is a compiler, not an unconditional Millennium claim.  The conditional
-- content is exactly the physical inhabitants supplied to H2/H5/C/H3/H6 and
-- their literal semantic interpretations above.
cmp119DirectPhysicalEndpointInstantiationLevel : ProofLevel
cmp119DirectPhysicalEndpointInstantiationLevel = conditional
