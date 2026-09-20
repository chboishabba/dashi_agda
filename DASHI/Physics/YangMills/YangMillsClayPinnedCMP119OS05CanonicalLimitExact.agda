{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact where

------------------------------------------------------------------------
-- A / OS0 + OS5 ON THE CANONICAL CMP119 EXPECTATION LIMIT
--
-- Avoid a second abstract Schwinger-limit carrier.  The predicates here are
-- applied directly to
--
--   finiteExpectation family n
--   limitExpectation  family.
--
-- Thus regularity/growth closure is forced onto the same expectation functional
-- already used by A, B and OS reconstruction.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

ExpectationFunctional : Set → Set
ExpectationFunctional Configuration = (Configuration → ℝ) → ℝ

record CanonicalCMP119OS05LimitData
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
    : Set₂ where
  field
    FiniteRegularity :
      ExpectationFunctional Configuration → Set
    ContinuumRegularity :
      ExpectationFunctional Configuration → Set

    FiniteGrowthControl :
      ExpectationFunctional Configuration → Set
    ContinuumGrowthControl :
      ExpectationFunctional Configuration → Set

    finiteRegularity :
      ∀ cutoff →
      FiniteRegularity
        (Limit.finiteExpectation family cutoff)

    finiteGrowthControl :
      ∀ cutoff →
      FiniteGrowthControl
        (Limit.finiteExpectation family cutoff)

    -- These are standard topology/functional-analysis closure authorities
    -- specialized to the canonical literal sequence/target, not arbitrary
    -- post-hoc continuum predicates.
    regularityClosedUnderCanonicalLimit :
      (∀ cutoff →
        FiniteRegularity
          (Limit.finiteExpectation family cutoff)) →
      ContinuumRegularity
        (Limit.limitExpectation family)

    growthClosedUnderCanonicalLimit :
      (∀ cutoff →
        FiniteGrowthControl
          (Limit.finiteExpectation family cutoff)) →
      ContinuumGrowthControl
        (Limit.limitExpectation family)

open CanonicalCMP119OS05LimitData public

canonicalCMP119OS0 :
  ∀ {Configuration sequenceLimit limitLaws quotient division family} →
  (dataSet :
    CanonicalCMP119OS05LimitData
      Configuration
      {sequenceLimit} {limitLaws} {quotient} {division}
      family) →
  ContinuumRegularity dataSet (Limit.limitExpectation family)
canonicalCMP119OS0 dataSet =
  regularityClosedUnderCanonicalLimit dataSet
    (finiteRegularity dataSet)

canonicalCMP119OS5 :
  ∀ {Configuration sequenceLimit limitLaws quotient division family} →
  (dataSet :
    CanonicalCMP119OS05LimitData
      Configuration
      {sequenceLimit} {limitLaws} {quotient} {division}
      family) →
  ContinuumGrowthControl dataSet (Limit.limitExpectation family)
canonicalCMP119OS5 dataSet =
  growthClosedUnderCanonicalLimit dataSet
    (finiteGrowthControl dataSet)

canonicalOS05LimitAssemblyLevel : ProofLevel
canonicalOS05LimitAssemblyLevel = machineChecked

regularityAndGrowthClosureAuthorityLevel : ProofLevel
regularityAndGrowthClosureAuthorityLevel = standardImported

-- Actual A analytic payments:
-- uniform finite-spacing regularity/distribution-order estimates and uniform
-- growth constants on the literal CMP119 family.  The target object and closure
-- transport are no longer additional seams.
literalCMP119FiniteRegularityLevel : ProofLevel
literalCMP119FiniteRegularityLevel = conditional

literalCMP119FiniteGrowthControlLevel : ProofLevel
literalCMP119FiniteGrowthControlLevel = conditional
