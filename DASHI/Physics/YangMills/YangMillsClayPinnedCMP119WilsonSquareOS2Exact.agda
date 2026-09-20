{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119WilsonSquareOS2Exact where

------------------------------------------------------------------------
-- A / LITERAL WILSON SQUARE FACTORIZATION -> PINNED CMP119 FINITE OS2
--
-- The pinned OS record historically asks directly for nonnegativity of every
-- finite reflected Gram quadratic form. For a Wilson/Haar lattice measure the
-- source theorem is stronger and more structured: the reflected form admits a
-- finite sum-of-squares factorization. FiniteReflectionPositivity already
-- proves that such a factorization is nonnegative.
--
-- This owner makes the exact same-object requirement explicit: the osForm in
-- the square factorization is the finite normalized CMP119 Gram quadratic form
-- for the selected cutoff/test family.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _≤ℝ_; ≤ℝ-refl; +-mono-≤)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.FiniteReflectionPositivity as FiniteRP
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as Pinned
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

realPositiveAdditiveScalar : FiniteRP.PositiveAdditiveScalar ℝ
realPositiveAdditiveScalar = record
  { FiniteRP.PositiveAdditiveScalar.zero = 0ℝ
  ; FiniteRP.PositiveAdditiveScalar.add = _+ℝ_
  ; FiniteRP.PositiveAdditiveScalar.Nonnegative = λ x → 0ℝ ≤ℝ x
  ; FiniteRP.PositiveAdditiveScalar.zeroNonnegative = ≤ℝ-refl
  ; FiniteRP.PositiveAdditiveScalar.addNonnegative = +-mono-≤
  }

record PinnedCMP119WilsonSquareFactorization
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum : Set}
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
    (inputs :
      Pinned.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    : Set₂ where
  field
    Interface : Set

    indices :
      ∀ group cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      List Interface

    squareTerm :
      ∀ group cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      Interface → ℝ

    squareTermNonnegative :
      ∀ group cutoff testFamily index →
      0ℝ ≤ℝ squareTerm group cutoff testFamily index

    peterWeylWilsonFactorization :
      ∀ group cutoff testFamily →
      Gram.physicalReflectedGramQuadraticForm
        (OS2.operations (Pinned.observableAlgebra inputs))
        (λ observable →
          Limit.finiteExpectation (Pinned.family inputs group) cutoff observable)
        testFamily
      ≡
      FiniteRP.sumTerms realPositiveAdditiveScalar
        (squareTerm group cutoff testFamily)
        (indices group cutoff testFamily)

open PinnedCMP119WilsonSquareFactorization public

asReflectionSquareFactorization :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S inputs}
    (factorization :
      PinnedCMP119WilsonSquareFactorization
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor} {Hilbert = Hilbert}
        {Hamiltonian = Hamiltonian} {Vacuum = Vacuum}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division} {S = S} inputs)
    group cutoff testFamily →
  FiniteRP.ReflectionSquareFactorization
    (Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ)
    (Interface factorization)
    ℝ
    realPositiveAdditiveScalar
asReflectionSquareFactorization {inputs = inputs}
    factorization group cutoff testFamily = record
  { FiniteRP.ReflectionSquareFactorization.indices =
      indices factorization group cutoff testFamily
  ; FiniteRP.ReflectionSquareFactorization.squareTerm =
      λ _ index → squareTerm factorization group cutoff testFamily index
  ; FiniteRP.ReflectionSquareFactorization.squareTermNonnegative =
      λ _ index → squareTermNonnegative factorization group cutoff testFamily index
  ; FiniteRP.ReflectionSquareFactorization.osForm =
      λ family →
        Gram.physicalReflectedGramQuadraticForm
          (OS2.operations (Pinned.observableAlgebra inputs))
          (λ observable →
            Limit.finiteExpectation (Pinned.family inputs group) cutoff observable)
          family
  ; FiniteRP.ReflectionSquareFactorization.factorization =
      λ _ → peterWeylWilsonFactorization factorization group cutoff testFamily
  }

finiteCMP119ReflectionPositiveFromWilsonSquares :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S inputs}
    (factorization :
      PinnedCMP119WilsonSquareFactorization
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor} {Hilbert = Hilbert}
        {Hamiltonian = Hamiltonian} {Vacuum = Vacuum}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division} {S = S} inputs) →
  ∀ group cutoff testFamily →
  0ℝ ≤ℝ
    Gram.physicalReflectedGramQuadraticForm
      (OS2.operations (Pinned.observableAlgebra inputs))
      (λ observable →
        Limit.finiteExpectation (Pinned.family inputs group) cutoff observable)
      testFamily
finiteCMP119ReflectionPositiveFromWilsonSquares factorization group cutoff testFamily =
  FiniteRP.osFormNonnegative
    (asReflectionSquareFactorization factorization group cutoff testFamily)
    testFamily

pinnedWilsonSquareToFiniteOS2CompilerLevel : ProofLevel
pinnedWilsonSquareToFiniteOS2CompilerLevel = machineChecked

literalCMP119WilsonPeterWeylFactorizationLevel : ProofLevel
literalCMP119WilsonPeterWeylFactorizationLevel = conditional
