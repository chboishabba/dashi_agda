{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119LiteralH2EndpointExact where

------------------------------------------------------------------------
-- EXACT H2 / FINITE-RG ENDPOINT ON THE SOURCE-CONSTRUCTED LITERAL Y.
--
-- Because Y is constructed directly from H2/H5, the endpoint finite and
-- continuum records consume H2's physical semantic proofs without any
-- post-hoc object equalities.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2Exact as H2
import DASHI.Physics.YangMills.YangMillsClayCMP119CompactSimplePhysicalH5Exact as H5
import DASHI.Physics.YangMills.YangMillsClayCMP119LiteralConstructionFromH5Exact as Literal
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

literalFiniteRG :
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
        limitLaws quotient division S h2 covarianceLaws h5) →
  Five.LiteralWeakCouplingRGConstruction
    (Literal.literalConstruction local)
literalFiniteRG {h2 = h2} local = record
  { Five.LiteralWeakCouplingRGConstruction.finiteVolumeCutoffMeasure =
      H2.finiteVolumeCutoffMeasure h2
  ; Five.LiteralWeakCouplingRGConstruction.reflectionPositiveRegularization =
      H2.reflectionPositiveRegularization h2
  ; Five.LiteralWeakCouplingRGConstruction.ultravioletYangMillsNormalization =
      H2.ultravioletYangMillsNormalization h2
  ; Five.LiteralWeakCouplingRGConstruction.asymptoticallyFreeScaleTrajectory =
      H2.asymptoticallyFreeScaleTrajectory h2
  ; Five.LiteralWeakCouplingRGConstruction.gaugeSymmetryPreserved =
      H2.gaugeSymmetryPreserved h2
  ; Five.LiteralWeakCouplingRGConstruction.localityPreserved =
      H2.localityPreserved h2
  ; Five.LiteralWeakCouplingRGConstruction.euclideanCovariancePreserved =
      H2.euclideanCovariancePreserved h2
  ; Five.LiteralWeakCouplingRGConstruction.reflectionPositivityPreserved =
      H2.reflectionPositivityPreserved h2
  ; Five.LiteralWeakCouplingRGConstruction.positivityNormalizationPreserved =
      H2.positivityNormalizationPreserved h2
  ; Five.LiteralWeakCouplingRGConstruction.volumeCutoffCompatibility =
      H2.volumeCutoffCompatibility h2
  }

literalContinuum :
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
        limitLaws quotient division S h2 covarianceLaws h5) →
  Five.UnifiedContinuumYMConstruction
    (Literal.literalConstruction local)
literalContinuum {h2 = h2} local = record
  { Five.UnifiedContinuumYMConstruction.continuumLimit =
      H2.continuumLimit h2
  ; Five.UnifiedContinuumYMConstruction.schwingerBelongsToContinuumMeasure =
      H2.schwingerBelongsToContinuumMeasure h2
  ; Five.UnifiedContinuumYMConstruction.acceptedWightmanOrOSAxioms =
      H2.acceptedWightmanOrOSAxioms h2
  ; Five.UnifiedContinuumYMConstruction.reconstructedHilbertSpace =
      H2.reconstructedHilbertSpaceMeaning h2
  ; Five.UnifiedContinuumYMConstruction.positiveSelfAdjointHamiltonian =
      H2.positiveSelfAdjointHamiltonianMeaning h2
  }

cmp119LiteralFiniteRGCompilerLevel : ProofLevel
cmp119LiteralFiniteRGCompilerLevel = machineChecked

cmp119LiteralContinuumCompilerLevel : ProofLevel
cmp119LiteralContinuumCompilerLevel = machineChecked
