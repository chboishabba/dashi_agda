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

------------------------------------------------------------------------
-- Pre-gap Wilson test presentation, on the SAME finite expectation family.
------------------------------------------------------------------------

record CMP119CoreSelectedWilsonPresentation
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
    (core :
      A.PinnedCMP119OSCoreInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : G)
    (tests :
      R278.SelectedConnectedCovarianceTests
        (Carrier.cmp119PhysicalMeasureConvergenceDataFromFamily
          (A.familyCore core group)
          (A.observableAlgebraCore core))) : Set₂ where
  field
    wilsonCore :
      Wilson.WilsonCylinderBoundData
        Loop (Configuration → ℝ) ℝ

    leftLoopsCore rightLoopsCore :
      R278.Index tests → List Loop

    selectedLeftIsWilsonProductCore :
      ∀ index →
      R278.left tests index
      ≡ Wilson.productLoopObservable wilsonCore (leftLoopsCore index)

    selectedRightIsWilsonProductCore :
      ∀ index →
      R278.right tests index
      ≡ Wilson.productLoopObservable wilsonCore (rightLoopsCore index)

    wilsonMultiplyIsCMP119MultiplyCore :
      ∀ left right →
      Wilson.multiplyObservable wilsonCore left right
      ≡ Gram.multiplyObservable
          (Gram.operations
            (Carrier.cmp119PhysicalMeasureConvergenceDataFromFamily
              (A.familyCore core group)
              (A.observableAlgebraCore core))) left right

open CMP119CoreSelectedWilsonPresentation public

coreWilsonAsLegacy :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Loop
      sequenceLimit limitLaws quotient division S}
    (core :
      A.PinnedCMP119OSCoreInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (clustering : A.CMP119OS4Attachment core)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : G)
    (tests :
      R278.SelectedConnectedCovarianceTests
        (Carrier.cmp119PhysicalMeasureConvergenceDataFromFamily
          (A.familyCore core group)
          (A.observableAlgebraCore core))) →
  CMP119CoreSelectedWilsonPresentation
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Loop
    core group tests →
  CMP119RealSelectedWilsonPresentation
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Loop
    (A.corePlusOS4Inputs core clustering)
    covarianceLaws group tests
coreWilsonAsLegacy core clustering covarianceLaws group tests source = record
  { CMP119RealSelectedWilsonPresentation.wilson =
      wilsonCore source
  ; CMP119RealSelectedWilsonPresentation.leftLoops =
      leftLoopsCore source
  ; CMP119RealSelectedWilsonPresentation.rightLoops =
      rightLoopsCore source
  ; CMP119RealSelectedWilsonPresentation.selectedLeftIsWilsonProduct =
      selectedLeftIsWilsonProductCore source
  ; CMP119RealSelectedWilsonPresentation.selectedRightIsWilsonProduct =
      selectedRightIsWilsonProductCore source
  ; CMP119RealSelectedWilsonPresentation.wilsonMultiplyIsCMP119Multiply =
      wilsonMultiplyIsCMP119MultiplyCore source
  }


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

cmp119CoreSelectedWilsonCompilerLevel : ProofLevel
cmp119CoreSelectedWilsonCompilerLevel = machineChecked

cmp119RealSelectedWilsonH2CompilerLevel : ProofLevel
cmp119RealSelectedWilsonH2CompilerLevel = machineChecked

-- Physical H2b is exactly this same-object Wilson-cylinder presentation.
-- Boundedness and all three expectation limits are definitional/compiler-owned
-- on the actual CMP119 convergence carrier.
cmp119RealSelectedWilsonH2PhysicalPresentationLevel : ProofLevel
cmp119RealSelectedWilsonH2PhysicalPresentationLevel = conditional
