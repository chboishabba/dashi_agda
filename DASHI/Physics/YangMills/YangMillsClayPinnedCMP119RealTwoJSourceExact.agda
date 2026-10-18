{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealTwoJSourceExact where

------------------------------------------------------------------------
-- REAL NORMALIZED TWO-J SOURCE CALCULUS ON THE LITERAL CMP119 FAMILY
--
-- Generic calculus proves
--
--   D_F D_G log Z = <FG> - <F><G>
--
-- on the exact finite real CMP119 expectation family.  Thus the only genuine
-- source theorem left in L4 is that the published CMP116 J coordinates are
-- these physical observable insertions and that the absolute differentiated
-- localization theorem applies to them.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _*ℝ_; _-ℝ_; absℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

realFiniteMomentAlgebra :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    (a :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (group : G) →
  Cumulant.TwoSourceMomentAlgebra
    (Configuration → ℝ)
    (Nat → ℝ)
realFiniteMomentAlgebra a group = record
  { Cumulant.TwoSourceMomentAlgebra.subtract =
      λ left right cutoff → left cutoff -ℝ right cutoff
  ; Cumulant.TwoSourceMomentAlgebra.multiply =
      λ left right cutoff → left cutoff *ℝ right cutoff
  ; Cumulant.TwoSourceMomentAlgebra.productObservable =
      λ left right configuration →
        left configuration *ℝ right configuration
  ; Cumulant.TwoSourceMomentAlgebra.expectation =
      λ observable cutoff →
        Limit.finiteExpectation (A.family a group) cutoff observable
  }

record LiteralRealTwoJSourceMeaning
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     Hilbert Hamiltonian Vacuum SourceDirection : Set)
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
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (group : CompactSimpleGroup) : Set₂ where
  field
    calculus :
      Cumulant.NormalizedLogSourceCalculus
        (realFiniteMomentAlgebra a group)

    meaning :
      Cumulant.LiteralTwoSourceInsertionMeaning
        calculus SourceDirection

open LiteralRealTwoJSourceMeaning public

finiteLiteralMixedLogIsConnectedCovariance :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum SourceDirection
      sequenceLimit limitLaws quotient division S a group}
    (source :
      LiteralRealTwoJSourceMeaning
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum SourceDirection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a group)
    cutoff left right →
  Cumulant.literalMixedSecondLogDerivative
    (meaning source)
    (Cumulant.sourceDirectionOf (meaning source) left)
    (Cumulant.sourceDirectionOf (meaning source) right)
    cutoff
  ≡
  Limit.finiteExpectation (A.family a group) cutoff
    (λ configuration → left configuration *ℝ right configuration)
  -ℝ
  Limit.finiteExpectation (A.family a group) cutoff left
  *ℝ
  Limit.finiteExpectation (A.family a group) cutoff right
finiteLiteralMixedLogIsConnectedCovariance source cutoff left right =
  cong
    (λ response → response cutoff)
    (Cumulant.literalMixedLogDerivativeIsConnectedCovariance
      (meaning source) left right)

finiteLiteralMixedLogMagnitudeIsPhysicalCovariance :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum SourceDirection
      sequenceLimit limitLaws quotient division S a group}
    (source :
      LiteralRealTwoJSourceMeaning
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum SourceDirection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a group)
    cutoff left right →
  absℝ
    (Cumulant.literalMixedSecondLogDerivative
      (meaning source)
      (Cumulant.sourceDirectionOf (meaning source) left)
      (Cumulant.sourceDirectionOf (meaning source) right)
      cutoff)
  ≡
  absℝ
    (Limit.finiteExpectation (A.family a group) cutoff
      (λ configuration → left configuration *ℝ right configuration)
    -ℝ
    Limit.finiteExpectation (A.family a group) cutoff left
    *ℝ
    Limit.finiteExpectation (A.family a group) cutoff right)
finiteLiteralMixedLogMagnitudeIsPhysicalCovariance source cutoff left right =
  cong absℝ
    (finiteLiteralMixedLogIsConnectedCovariance
      source cutoff left right)

realTwoJConnectedCumulantCompilerLevel : ProofLevel
realTwoJConnectedCumulantCompilerLevel = machineChecked

realTwoJMagnitudeCompilerLevel : ProofLevel
realTwoJMagnitudeCompilerLevel = machineChecked

-- This is now the sole L4 source/application leaf:
-- identify the published CMP116 J direction with sourceDirectionOf meaning.
literalCMP116PhysicalJDirectionMeaningLevel : ProofLevel
literalCMP116PhysicalJDirectionMeaningLevel = conditional
