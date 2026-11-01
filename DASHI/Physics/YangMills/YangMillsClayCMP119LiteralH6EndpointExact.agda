{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119LiteralH6EndpointExact where

------------------------------------------------------------------------
-- H6 ENDPOINT ON THE SOURCE-CONSTRUCTED LITERAL Y.
--
-- Every group consumes its exact H5 package, exact H2 OS system, exact H3 gap,
-- and the ONE DirectPhysicalCSource attached to Y.  The Round77 interacting
-- witness is constructed; only its interpretation as the literal Clay
-- nontriviality predicates remains physical.
------------------------------------------------------------------------

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
import DASHI.Physics.YangMills.YangMillsClayDirectPhysicalCExact as DirectC
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectSameSystemH6Exact as H6
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119LiteralH6Semantics
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
    (cSource :
      DirectC.DirectPhysicalCSource
        (Literal.literalConstruction local))
    : Set₂ where
  private
    Y = Literal.literalConstruction local

  field
    h6ForGroup :
      ∀ group →
      let package = H5.physicalPackageForLiteralGroup h5 group
      in
      H6.CMP119DirectSameSystemH6
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        (H5.SourceScale package)
        (H5.SourceVolume package)
        (H5.SourceRoot package)
        (H5.SourceDirection' package)
        (H5.SpectralObservable' package)
        ContinuumFamily
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S Y h2 covarianceLaws group
        (H5.publishedCMP116 package)
        (H5.realSelected package)
        (H5.sameOSH3 package)
        (H5.positiveGapCandidate package)
        cSource

    witnessMeansLiteralNontriviality :
      ∀ group →
      let package = H5.physicalPackageForLiteralGroup h5 group
          h6 = h6ForGroup group
      in
      OS.InteractingContinuumWitness
        (Configuration → ℝ) Position ℝ
        (OSSystem.continuumOSSystem (H2.osInputs h2) group) →
      Top.IsNontrivialQuantumYangMills S group
        (Top.continuumMeasure Y group)
        (Top.schwinger Y group)

    witnessMeansPreservedInLiteralLimit :
      ∀ group →
      OS.InteractingContinuumWitness
        (Configuration → ℝ) Position ℝ
        (OSSystem.continuumOSSystem (H2.osInputs h2) group) →
      Top.NontrivialityPreservedInLimit S group
        (Top.continuumMeasure Y group)

open CMP119LiteralH6Semantics public

literalNontriviality :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      ContinuumFamily sequenceLimit limitLaws quotient division S h2
      covarianceLaws h5 local cSource} →
  CMP119LiteralH6Semantics
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    LieElement GroupElement ContinuumFamily
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S h2 covarianceLaws h5 local cSource →
  Five.InteractingContinuumNontriviality
    (Literal.literalConstruction local)
literalNontriviality semantics = record
  { Five.InteractingContinuumNontriviality.nontrivialQuantumYangMills =
      λ group →
        witnessMeansLiteralNontriviality semantics group
          (H6.interactingWitness
            (h6ForGroup semantics group))
  ; Five.InteractingContinuumNontriviality.nontrivialityPreservedInLimit =
      λ group →
        witnessMeansPreservedInLiteralLimit semantics group
          (H6.interactingWitness
            (h6ForGroup semantics group))
  }

cmp119LiteralH6EndpointCompilerLevel : ProofLevel
cmp119LiteralH6EndpointCompilerLevel = machineChecked

cmp119LiteralH6SemanticInterpretationLevel : ProofLevel
cmp119LiteralH6SemanticInterpretationLevel = conditional
