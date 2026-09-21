{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayT5MomentToOS05Round464Exact where

------------------------------------------------------------------------
-- GOAL-1 A4/A5 / ROUND464:
-- QUANTITATIVE T5 MOMENTS/DISTRIBUTION ORDER -> CANONICAL OS0/OS5.
--
-- The T5 thermodynamic lane already contains the quantitative machinery:
--   * cutoff-uniform exponential insertion moments;
--   * all finite polynomial moments;
--   * uniform integrability of reflected products;
--   * uniform distribution-order / Schwinger bounds when supplied physically.
--
-- CanonicalCMP119OS05LimitData already proves closure of finite OS0/OS5 data
-- onto the SAME canonical expectation limit.
--
-- Therefore the remaining Goal-1 A4/A5 payment is not two independent
-- continuum theorems.  It is one semantic/analytic bridge saying that the
-- concrete quantitative finite-family estimates imply the finite regularity
-- and growth predicates required by the selected OS theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as OS05
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record QuantitativeMomentOS05Bridge
    (Configuration Measure : Set)
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
    : Set₂ where
  field
    quantitative :
      T5.PhysicalExpectationProducerData
        Measure (Configuration → ℝ) ℝ

    -- Same-family attachment: the T5 diagonal expectation sequence is the
    -- finite CMP119 expectation sequence used by the pinned OS construction.
    quantitativeFiniteExpectationIsCMP119 :
      ∀ cutoff observable →
      Gram.expectation
        (T5.operations (T5.thermodynamic quantitative))
        (T5.diagonalMeasure quantitative cutoff)
        observable
      ≡
      Limit.finiteExpectation family cutoff observable

    -- We intentionally keep the final OS vocabulary explicit.  These predicates
    -- are selected by the human OS theorem, not manufactured by the compiler.
    FiniteRegularity :
      OS05.ExpectationFunctional Configuration → Set
    ContinuumRegularity :
      OS05.ExpectationFunctional Configuration → Set
    FiniteGrowthControl :
      OS05.ExpectationFunctional Configuration → Set
    ContinuumGrowthControl :
      OS05.ExpectationFunctional Configuration → Set

    -- Physical A4/A5 bridge.  These are the only genuinely new implications:
    -- the already-proved quantitative moment/distribution estimates imply the
    -- chosen finite OS0/OS5 predicates.
    quantitativeBoundsImplyFiniteRegularity :
      ∀ cutoff →
      FiniteRegularity (Limit.finiteExpectation family cutoff)

    quantitativeBoundsImplyFiniteGrowth :
      ∀ cutoff →
      FiniteGrowthControl (Limit.finiteExpectation family cutoff)

    -- Standard closure authorities for the selected OS0/OS5 definitions.
    regularityClosedUnderCanonicalLimit :
      (∀ cutoff →
        FiniteRegularity (Limit.finiteExpectation family cutoff)) →
      ContinuumRegularity (Limit.limitExpectation family)

    growthClosedUnderCanonicalLimit :
      (∀ cutoff →
        FiniteGrowthControl (Limit.finiteExpectation family cutoff)) →
      ContinuumGrowthControl (Limit.limitExpectation family)

open QuantitativeMomentOS05Bridge public

asCanonicalOS05 :
  ∀ {Configuration Measure
      sequenceLimit limitLaws quotient division family} →
  QuantitativeMomentOS05Bridge
    Configuration Measure
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family →
  OS05.CanonicalCMP119OS05LimitData
    Configuration
    {sequenceLimit}
    {limitLaws}
    {quotient}
    {division}
    family
asCanonicalOS05 bridge = record
  { OS05.CanonicalCMP119OS05LimitData.FiniteRegularity =
      FiniteRegularity bridge
  ; OS05.CanonicalCMP119OS05LimitData.ContinuumRegularity =
      ContinuumRegularity bridge
  ; OS05.CanonicalCMP119OS05LimitData.FiniteGrowthControl =
      FiniteGrowthControl bridge
  ; OS05.CanonicalCMP119OS05LimitData.ContinuumGrowthControl =
      ContinuumGrowthControl bridge
  ; OS05.CanonicalCMP119OS05LimitData.finiteRegularity =
      quantitativeBoundsImplyFiniteRegularity bridge
  ; OS05.CanonicalCMP119OS05LimitData.finiteGrowthControl =
      quantitativeBoundsImplyFiniteGrowth bridge
  ; OS05.CanonicalCMP119OS05LimitData.regularityClosedUnderCanonicalLimit =
      regularityClosedUnderCanonicalLimit bridge
  ; OS05.CanonicalCMP119OS05LimitData.growthClosedUnderCanonicalLimit =
      growthClosedUnderCanonicalLimit bridge
  }

continuumOS0FromQuantitativeMoments :
  ∀ {Configuration Measure
      sequenceLimit limitLaws quotient division family}
    (bridge :
      QuantitativeMomentOS05Bridge
        Configuration Measure
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family) →
  ContinuumRegularity bridge (Limit.limitExpectation family)
continuumOS0FromQuantitativeMoments bridge =
  OS05.canonicalCMP119OS0 (asCanonicalOS05 bridge)

continuumOS5FromQuantitativeMoments :
  ∀ {Configuration Measure
      sequenceLimit limitLaws quotient division family}
    (bridge :
      QuantitativeMomentOS05Bridge
        Configuration Measure
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family) →
  ContinuumGrowthControl bridge (Limit.limitExpectation family)
continuumOS5FromQuantitativeMoments bridge =
  OS05.canonicalCMP119OS5 (asCanonicalOS05 bridge)

round464OS05AssemblyCompilerLevel : ProofLevel
round464OS05AssemblyCompilerLevel = machineChecked

round464OS05ClosureAuthorityLevel : ProofLevel
round464OS05ClosureAuthorityLevel =
  OS05.regularityAndGrowthClosureAuthorityLevel

-- The actual remaining A4/A5 mathematics is exactly the pair of implications
-- quantitativeBoundsImplyFiniteRegularity / quantitativeBoundsImplyFiniteGrowth
-- on the literal CMP119 family.  Continuum closure is not another leaf.
literalRound464QuantitativeMomentToOS05Level : ProofLevel
literalRound464QuantitativeMomentToOS05Level = conditional
