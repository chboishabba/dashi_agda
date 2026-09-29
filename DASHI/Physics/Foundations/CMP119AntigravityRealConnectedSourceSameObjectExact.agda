{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealConnectedSourceSameObjectExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _*ℝ_; _-ℝ_)

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealTwoJSourceExact as TwoJ
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant

------------------------------------------------------------------------
-- SELECTED CMP119 SOURCE -> CANONICAL REAL WILSON/GIBBS CONNECTED COVARIANCE
--
-- The physical real CMP119 lane already proves:
--
--   literal mixed J-log derivative
--     = <FG> - <F><G>
--
-- on the SAME finite normalized CMP119 family.
--
-- Therefore antigravity does not need a second connected-covariance theorem.
-- The only source-bearing attachment is that its selected stress direction is
-- the literal J-direction already owned by the real CMP119 source calculus.
------------------------------------------------------------------------

record SelectedRealCMP119ConnectedSourceWeld
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum SourceDirection : Set}
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
    {group : G}
    (source :
      TwoJ.LiteralRealTwoJSourceMeaning
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum SourceDirection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S} a group)
    (cutoff : Nat)
    (left right : Configuration → ℝ) : Set₁ where
  field
    selectedCMP119ConnectedSource : ℝ

    selectedSourceIsLiteralMixedLogDerivative :
      selectedCMP119ConnectedSource
      ≡
      Cumulant.literalMixedSecondLogDerivative
        (TwoJ.meaning source)
        (Cumulant.sourceDirectionOf (TwoJ.meaning source) left)
        (Cumulant.sourceDirectionOf (TwoJ.meaning source) right)
        cutoff

open SelectedRealCMP119ConnectedSourceWeld public

selectedCMP119ConnectedSourceIsCanonicalWilsonGibbsCovariance :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum SourceDirection
      sequenceLimit limitLaws quotient division S a group}
    {source :
      TwoJ.LiteralRealTwoJSourceMeaning
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum SourceDirection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S} a group}
    {cutoff : Nat}
    {left right : Configuration → ℝ}
    (weld :
      SelectedRealCMP119ConnectedSourceWeld source cutoff left right) →
  selectedCMP119ConnectedSource weld
  ≡
  Limit.finiteExpectation (A.family a group) cutoff
      (λ configuration → left configuration *ℝ right configuration)
  -ℝ
  Limit.finiteExpectation (A.family a group) cutoff left
  *ℝ
  Limit.finiteExpectation (A.family a group) cutoff right
selectedCMP119ConnectedSourceIsCanonicalWilsonGibbsCovariance
    {source = source} {cutoff = cutoff} {left = left} {right = right} weld =
  trans
    (selectedSourceIsLiteralMixedLogDerivative weld)
    (TwoJ.finiteLiteralMixedLogIsConnectedCovariance
      source cutoff left right)
