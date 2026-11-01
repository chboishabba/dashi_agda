{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StandaloneWilsonSquareExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _≤ℝ_; ≤ℝ-refl; +-mono-≤)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.FiniteReflectionPositivity as FiniteRP
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
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

record StandaloneCMP119WilsonSquare
    (Configuration : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    (algebra : OS2.CylinderOSAlgebra (Configuration → ℝ))
    : Set₂ where
  field
    Interface : Set

    indices :
      ∀ cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      List Interface

    squareTerm :
      ∀ cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      Interface → ℝ

    squareTermNonnegative :
      ∀ cutoff testFamily index →
      0ℝ ≤ℝ squareTerm cutoff testFamily index

    peterWeylWilsonFactorization :
      ∀ cutoff testFamily →
      Gram.physicalReflectedGramQuadraticForm
        (OS2.operations algebra)
        (λ observable →
          Limit.finiteExpectation family cutoff observable)
        testFamily
      ≡
      FiniteRP.sumTerms realPositiveAdditiveScalar
        (squareTerm cutoff testFamily)
        (indices cutoff testFamily)

open StandaloneCMP119WilsonSquare public

asReflectionSquareFactorization :
  ∀ {Configuration sequenceLimit limitLaws quotient division family algebra}
    (dataSet :
      StandaloneCMP119WilsonSquare
        Configuration
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family algebra)
    cutoff testFamily →
  FiniteRP.ReflectionSquareFactorization
    (Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ)
    (Interface dataSet)
    ℝ
    realPositiveAdditiveScalar
asReflectionSquareFactorization
    {family = family} {algebra = algebra}
    dataSet cutoff testFamily = record
  { FiniteRP.ReflectionSquareFactorization.indices =
      indices dataSet cutoff testFamily
  ; FiniteRP.ReflectionSquareFactorization.squareTerm =
      λ _ index → squareTerm dataSet cutoff testFamily index
  ; FiniteRP.ReflectionSquareFactorization.squareTermNonnegative =
      λ _ index → squareTermNonnegative dataSet cutoff testFamily index
  ; FiniteRP.ReflectionSquareFactorization.osForm =
      λ selectedFamily →
        Gram.physicalReflectedGramQuadraticForm
          (OS2.operations algebra)
          (λ observable →
            Limit.finiteExpectation family cutoff observable)
          selectedFamily
  ; FiniteRP.ReflectionSquareFactorization.factorization =
      λ _ → peterWeylWilsonFactorization dataSet cutoff testFamily
  }

finiteReflectionPositive :
  ∀ {Configuration sequenceLimit limitLaws quotient division family algebra}
    (dataSet :
      StandaloneCMP119WilsonSquare
        Configuration
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family algebra)
    cutoff testFamily →
  0ℝ ≤ℝ
    Gram.physicalReflectedGramQuadraticForm
      (OS2.operations algebra)
      (λ observable →
        Limit.finiteExpectation family cutoff observable)
      testFamily
finiteReflectionPositive dataSet cutoff testFamily =
  FiniteRP.osFormNonnegative
    (asReflectionSquareFactorization dataSet cutoff testFamily)
    testFamily

standaloneWilsonSquareCompilerLevel : ProofLevel
standaloneWilsonSquareCompilerLevel = machineChecked

literalStandaloneWilsonSquareIdentificationLevel : ProofLevel
literalStandaloneWilsonSquareIdentificationLevel = conditional
