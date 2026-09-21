{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsCMP119PeterWeylWilsonSquareRound444Exact where

------------------------------------------------------------------------
-- A / ROUND444: POSITIVE PETER-WEYL COEFFICIENTS -> FINITE WILSON OS SQUARE
--
-- The finite reflection-positivity input should not separately assume
-- "squareTermNonnegative".  On the Wilson/Peter-Weyl route every interface term
-- has the literal form
--
--                   c_lambda * A_lambda^2
--
-- with c_lambda >= 0.  This owner derives positivity of each term and compiles
-- the exact StandaloneCMP119WilsonSquare used by R436.
--
-- Remaining A2 source mathematics:
--   (1) identify the literal cross-plane Wilson weight with this Peter-Weyl
--       finite sum of squares;
--   (2) prove the selected character coefficients are nonnegative.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _*ℝ_ ; _≤ℝ_
  ; ≤ℝ-refl ; mulMonotoneNonnegative ; mulZeroʳ )
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Closure.NSPeriodicRealOrderedNormLaws as Square
import DASHI.Physics.YangMills.FiniteReflectionPositivity as FiniteRP
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StandaloneWilsonSquareExact as Wilson
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119PeterWeylWilsonSquare
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
    squareOrder : Square.OrderedRealSquareAuthority

    Interface : Set

    indices :
      ∀ cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      List Interface

    characterCoefficient :
      ∀ cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      Interface → ℝ

    reflectedAmplitude :
      ∀ cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      Interface → ℝ

    characterCoefficientNonnegative :
      ∀ cutoff testFamily index →
      0ℝ ≤ℝ characterCoefficient cutoff testFamily index

    -- The source-specific Wilson/Peter-Weyl identity on the SAME finite family.
    peterWeylWilsonFactorization :
      ∀ cutoff testFamily →
      Gram.physicalReflectedGramQuadraticForm
        (OS2.operations algebra)
        (λ observable →
          Limit.finiteExpectation family cutoff observable)
        testFamily
      ≡
      FiniteRP.sumTerms Wilson.realPositiveAdditiveScalar
        (λ index →
          characterCoefficient cutoff testFamily index *ℝ
            (reflectedAmplitude cutoff testFamily index *ℝ
             reflectedAmplitude cutoff testFamily index))
        (indices cutoff testFamily)

open CMP119PeterWeylWilsonSquare public

squareTerm :
  ∀ {Configuration sequenceLimit limitLaws quotient division family algebra} →
  CMP119PeterWeylWilsonSquare
    Configuration
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family algebra →
  ∀ cutoff
    (testFamily :
      Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
  Interface _ → ℝ
squareTerm dataSet cutoff testFamily index =
  characterCoefficient dataSet cutoff testFamily index *ℝ
    (reflectedAmplitude dataSet cutoff testFamily index *ℝ
     reflectedAmplitude dataSet cutoff testFamily index)

squareTermNonnegative :
  ∀ {Configuration sequenceLimit limitLaws quotient division family algebra}
    (dataSet :
      CMP119PeterWeylWilsonSquare
        Configuration
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family algebra)
    cutoff testFamily index →
  0ℝ ≤ℝ squareTerm dataSet cutoff testFamily index
squareTermNonnegative dataSet cutoff testFamily index =
  let
    coefficientNN =
      characterCoefficientNonnegative dataSet cutoff testFamily index

    amplitudeSquareNN =
      Square.squareNonnegative
        (squareOrder dataSet)
        (reflectedAmplitude dataSet cutoff testFamily index)

    productNN :
      0ℝ *ℝ 0ℝ
      ≤ℝ squareTerm dataSet cutoff testFamily index
    productNN =
      mulMonotoneNonnegative
        ≤ℝ-refl coefficientNN
        ≤ℝ-refl amplitudeSquareNN
  in
  subst
    (λ lower → lower ≤ℝ squareTerm dataSet cutoff testFamily index)
    (mulZeroʳ 0ℝ)
    productNN

asStandaloneWilsonSquare :
  ∀ {Configuration sequenceLimit limitLaws quotient division family algebra} →
  CMP119PeterWeylWilsonSquare
    Configuration
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family algebra →
  Wilson.StandaloneCMP119WilsonSquare
    Configuration family algebra
asStandaloneWilsonSquare dataSet = record
  { Wilson.StandaloneCMP119WilsonSquare.Interface =
      Interface dataSet
  ; Wilson.StandaloneCMP119WilsonSquare.indices =
      indices dataSet
  ; Wilson.StandaloneCMP119WilsonSquare.squareTerm =
      squareTerm dataSet
  ; Wilson.StandaloneCMP119WilsonSquare.squareTermNonnegative =
      squareTermNonnegative dataSet
  ; Wilson.StandaloneCMP119WilsonSquare.peterWeylWilsonFactorization =
      peterWeylWilsonFactorization dataSet
  }

round444SquareTermPositivityCompilerLevel : ProofLevel
round444SquareTermPositivityCompilerLevel = machineChecked

round444StandaloneWilsonSquareCompilerLevel : ProofLevel
round444StandaloneWilsonSquareCompilerLevel = machineChecked

-- A2 is now one representation-theoretic/source identification theorem plus
-- positivity of the Wilson character coefficients.  Finite and continuum OS2
-- positivity are downstream.
literalRound444PeterWeylWilsonIdentificationLevel : ProofLevel
literalRound444PeterWeylWilsonIdentificationLevel = conditional
