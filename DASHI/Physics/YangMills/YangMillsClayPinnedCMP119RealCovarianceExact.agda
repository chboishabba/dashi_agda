{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact where

------------------------------------------------------------------------
-- SAME CMP119 REAL EXPECTATION LIMIT -> REAL CONNECTED COVARIANCE LIMIT
--
-- This is the literal-A/B covariance carrier.  No rational surrogate and no
-- second continuum measure are used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (tt)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _-ℝ_; absℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CanonicalRealCovarianceLimitLaws
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError) : Set₁ where
  field
    multiplyLimit :
      ∀ left right →
      Seq.limit sequenceLimit
        (λ n → left n *ℝ right n)
      ≡
      Seq.limit sequenceLimit left *ℝ Seq.limit sequenceLimit right

    negateLimit :
      ∀ sequence →
      Seq.limit sequenceLimit
        (λ n → 0ℝ -ℝ sequence n)
      ≡
      0ℝ -ℝ Seq.limit sequenceLimit sequence

    absoluteLimit :
      ∀ sequence →
      Seq.limit sequenceLimit
        (λ n → absℝ (sequence n))
      ≡
      absℝ (Seq.limit sequenceLimit sequence)

open CanonicalRealCovarianceLimitLaws public

realCovarianceExtension :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : G) →
  R278.ScalarCovarianceConvergenceExtension
    (Carrier.cmp119PhysicalMeasureConvergenceData inputs group)
realCovarianceExtension
    {sequenceLimit = sequenceLimit}
    inputs covarianceLaws group = record
  { R278.ScalarCovarianceConvergenceExtension.negate =
      λ value → 0ℝ -ℝ value
  ; R278.ScalarCovarianceConvergenceExtension.magnitude =
      absℝ
  ; R278.ScalarCovarianceConvergenceExtension.multiplyConverges =
      λ left right leftLimit rightLimit leftConv rightConv →
        transLimit
          (multiplyLimit covarianceLaws left right)
          leftConv rightConv
  ; R278.ScalarCovarianceConvergenceExtension.negateConverges =
      λ sequence limit converges →
        transportUnary
          (negateLimit covarianceLaws sequence)
          converges
  ; R278.ScalarCovarianceConvergenceExtension.magnitudeConverges =
      λ sequence limit converges →
        transportUnary
          (absoluteLimit covarianceLaws sequence)
          converges
  }
  where
  transLimit :
    ∀ {left right : Nat → ℝ} {leftLimit rightLimit : ℝ} →
    Seq.limit sequenceLimit
      (λ n → left n *ℝ right n)
      ≡
      Seq.limit sequenceLimit left *ℝ Seq.limit sequenceLimit right →
    Seq.limit sequenceLimit left ≡ leftLimit →
    Seq.limit sequenceLimit right ≡ rightLimit →
    Seq.limit sequenceLimit
      (λ n → left n *ℝ right n)
      ≡ leftLimit *ℝ rightLimit
  transLimit productLaw leftConv rightConv
    rewrite leftConv | rightConv = productLaw

  transportUnary :
    ∀ {sequence : Nat → ℝ} {target : ℝ}
      {op : ℝ → ℝ} →
    Seq.limit sequenceLimit (λ n → op (sequence n))
      ≡ op (Seq.limit sequenceLimit sequence) →
    Seq.limit sequenceLimit sequence ≡ target →
    Seq.limit sequenceLimit (λ n → op (sequence n))
      ≡ op target
  transportUnary law converges rewrite converges = law

selectedTests :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (group : G)
    (Index : Set)
    (left right : Index → Configuration → ℝ) →
  R278.SelectedConnectedCovarianceTests
    (Carrier.cmp119PhysicalMeasureConvergenceData inputs group)
selectedTests inputs group Index left right = record
  { R278.SelectedConnectedCovarianceTests.Index = Index
  ; R278.SelectedConnectedCovarianceTests.left = left
  ; R278.SelectedConnectedCovarianceTests.right = right
  ; R278.SelectedConnectedCovarianceTests.leftBounded =
      λ index → tt
  ; R278.SelectedConnectedCovarianceTests.rightBounded =
      λ index → tt
  ; R278.SelectedConnectedCovarianceTests.productBounded =
      λ index → tt
  }

selectedRealConnectedCovarianceConverges :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : G)
    (Index : Set)
    (left right : Index → Configuration → ℝ)
    (index : Index) →
  Gram.Converges
    (Gram.scalarConvergence
      (Carrier.cmp119PhysicalMeasureConvergenceData inputs group))
    (λ cutoff →
      R278.connectedCovarianceMagnitude
        (realCovarianceExtension inputs covarianceLaws group)
        (Gram.measureSequence
          (Carrier.cmp119PhysicalMeasureConvergenceData inputs group)
          cutoff)
        (left index) (right index))
    (R278.connectedCovarianceMagnitude
      (realCovarianceExtension inputs covarianceLaws group)
      (Gram.continuumMeasure
        (Carrier.cmp119PhysicalMeasureConvergenceData inputs group))
      (left index) (right index))
selectedRealConnectedCovarianceConverges
    inputs covarianceLaws group Index left right index =
  R278.selectedConnectedCovarianceMagnitudeConverges
    (realCovarianceExtension inputs covarianceLaws group)
    (selectedTests inputs group Index left right)
    index

pinnedCMP119RealCovarianceLimitCompilerLevel : ProofLevel
pinnedCMP119RealCovarianceLimitCompilerLevel = machineChecked

canonicalRealCovarianceLimitLawsLevel : ProofLevel
canonicalRealCovarianceLimitLawsLevel = standardImported
