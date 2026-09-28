{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedWilsonH2Exact where

------------------------------------------------------------------------
-- H2b ON THE ACTUAL REAL CMP119 COVARIANCE CARRIER.
--
-- On this carrier BoundedObservable = top definitionally.  Therefore the only
-- physical payment is same-object presentation:
--
--   selected left  = finite Wilson-cylinder product
--   selected right = finite Wilson-cylinder product
--   selected multiplication = the CMP119 observable multiplication.
--
-- The three selected expectation limits are then compiler output from R278.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Unit using (tt)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Wilson
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119RealSelectedWilsonPresentation
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Loop : Set)
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
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : G)
    (tests :
      R278.SelectedConnectedCovarianceTests
        (Carrier.cmp119PhysicalMeasureConvergenceData a group))
    : Set₂ where
  private
    dataSet = Carrier.cmp119PhysicalMeasureConvergenceData a group

  field
    wilson :
      Wilson.WilsonCylinderBoundData
        Loop (Configuration → ℝ) ℝ

    leftLoops rightLoops :
      R278.Index tests → List Loop

    selectedLeftIsWilsonProduct :
      ∀ index →
      R278.left tests index
      ≡ Wilson.productLoopObservable wilson (leftLoops index)

    selectedRightIsWilsonProduct :
      ∀ index →
      R278.right tests index
      ≡ Wilson.productLoopObservable wilson (rightLoops index)

    wilsonMultiplyIsCMP119Multiply :
      ∀ left right →
      Wilson.multiplyObservable wilson left right
      ≡ Gram.multiplyObservable
          (Gram.operations dataSet) left right

open CMP119RealSelectedWilsonPresentation public

record CMP119RealSelectedExpectationLimits
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Loop : Set)
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
    {a :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    {covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit}
    {group : G}
    {tests :
      R278.SelectedConnectedCovarianceTests
        (Carrier.cmp119PhysicalMeasureConvergenceData a group)}
    (presentation :
      CMP119RealSelectedWilsonPresentation
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Loop
        a covarianceLaws group tests)
    (index : R278.Index tests)
    : Set₁ where
  private
    dataSet = Carrier.cmp119PhysicalMeasureConvergenceData a group
    extension = Cov.realCovarianceExtension a covarianceLaws group

  field
    leftExpectationConverges :
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff →
          Gram.expectation (Gram.operations dataSet)
            (Gram.measureSequence dataSet cutoff)
            (R278.left tests index))
        (Gram.expectation (Gram.operations dataSet)
          (Gram.continuumMeasure dataSet)
          (R278.left tests index))

    rightExpectationConverges :
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff →
          Gram.expectation (Gram.operations dataSet)
            (Gram.measureSequence dataSet cutoff)
            (R278.right tests index))
        (Gram.expectation (Gram.operations dataSet)
          (Gram.continuumMeasure dataSet)
          (R278.right tests index))

    productExpectationConverges :
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff →
          Gram.expectation (Gram.operations dataSet)
            (Gram.measureSequence dataSet cutoff)
            (Gram.multiplyObservable (Gram.operations dataSet)
              (R278.left tests index)
              (R278.right tests index)))
        (Gram.expectation (Gram.operations dataSet)
          (Gram.continuumMeasure dataSet)
          (Gram.multiplyObservable (Gram.operations dataSet)
            (R278.left tests index)
            (R278.right tests index)))

open CMP119RealSelectedExpectationLimits public

selectedExpectationLimits :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Loop
      sequenceLimit limitLaws quotient division S
      a covarianceLaws group tests}
    (presentation :
      CMP119RealSelectedWilsonPresentation
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Loop
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        a covarianceLaws group tests)
    index →
  CMP119RealSelectedExpectationLimits
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Loop
    presentation index
selectedExpectationLimits
    {a = a} {covarianceLaws = covarianceLaws} {group = group}
    {tests = tests} presentation index =
  let
    dataSet = Carrier.cmp119PhysicalMeasureConvergenceData a group
  in
  record
    { CMP119RealSelectedExpectationLimits.leftExpectationConverges =
        R278.selectedExpectationConverges dataSet
          (R278.left tests index) tt
    ; CMP119RealSelectedExpectationLimits.rightExpectationConverges =
        R278.selectedExpectationConverges dataSet
          (R278.right tests index) tt
    ; CMP119RealSelectedExpectationLimits.productExpectationConverges =
        R278.selectedExpectationConverges dataSet
          (Gram.multiplyObservable (Gram.operations dataSet)
            (R278.left tests index) (R278.right tests index))
          tt
    }

cmp119RealSelectedWilsonH2CompilerLevel : ProofLevel
cmp119RealSelectedWilsonH2CompilerLevel = machineChecked

-- Physical H2b is exactly this same-object Wilson-cylinder presentation.
-- Boundedness and all three expectation limits are definitional/compiler-owned
-- on the actual CMP119 convergence carrier.
cmp119RealSelectedWilsonH2PhysicalPresentationLevel : ProofLevel
cmp119RealSelectedWilsonH2PhysicalPresentationLevel = conditional
