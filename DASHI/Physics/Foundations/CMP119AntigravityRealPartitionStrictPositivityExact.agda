{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealPartitionStrictPositivityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _≤ℝ_; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient

------------------------------------------------------------------------
-- Z > 0 WITHOUT A POSITIVE-NEIGHBORHOOD CONSTRUCTION
--
-- Literal physical integration already proves:
--
--   density >= 0  =>  integral density >= 0,
--   Z = integral density.
--
-- The normalized finite CMP119 family separately carries an abstract Nonzero
-- token for Z.  Once that token is given its standard semantic meaning
-- Z != 0, ordered-real separation gives Z > 0.
--
-- Hence the compact-Haar full-support / neighborhood theorem is needed only
-- for strict positivity of N(F^2), not for the partition function.
------------------------------------------------------------------------

partitionFunctionNonnegative :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ} →
  Finite.PhysicalFiniteMeasureIntegrationLaws measure →
  0ℝ ≤ℝ Physical.partitionFunction measure
partitionFunctionNonnegative {measure = measure} laws =
  subst
    (λ value → 0ℝ ≤ℝ value)
    (sym (Finite.partitionFunctionIsDensityIntegral laws))
    (Finite.haarIntegralPositive laws
      (Physical.density measure)
      (Finite.densityNonnegative laws))

record QuotientNonzeroSemantics
    {Converges}
    (authority : Quotient.RealQuotientConvergenceAuthority Converges) : Set₁ where
  field
    nonzeroMeansNotZero :
      ∀ value →
      Quotient.Nonzero authority value →
      value ≡ 0ℝ →
      Strict.Empty

open QuotientNonzeroSemantics public

partitionFunctionStrictlyPositive :
  ∀ {Configuration Converges authority}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (strict : Strict.RealStrictSignLaws)
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure)
    (semantics : QuotientNonzeroSemantics {Converges = Converges} authority) →
  Quotient.Nonzero authority (Physical.partitionFunction measure) →
  0ℝ <ℝ Physical.partitionFunction measure
partitionFunctionStrictlyPositive
    {measure = measure} strict laws semantics nonzero =
  Strict.nonnegativeNonzeroPositive strict
    (partitionFunctionNonnegative laws)
    (nonzeroMeansNotZero semantics
      (Physical.partitionFunction measure)
      nonzero)
