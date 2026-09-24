{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5MarkedMomentOS05Round446Exact where

------------------------------------------------------------------------
-- ROUND446 / MARKED-FP MOMENTS -> REAL CMP119 OS0/OS5 WITHOUT FAKE REAL PRODUCER
--
-- R464 carried a full real-valued PhysicalExpectationProducerData only as
-- provenance.  Its actual OS0/OS5 compiler consumes:
--
--   finite regularity on each literal real CMP119 expectation,
--   finite growth control on each literal real CMP119 expectation,
--   standard closure of those predicates under the canonical expectation limit.
--
-- The mature marked-FP theorem is rational-valued.  Rather than manufacture a
-- second real T5 moment producer, R446 keeps the actual remaining physical
-- theorem explicit:
--
--   the selected marked-FP moment estimates imply the chosen finite REAL OS0
--   and OS5 predicates on the literal CMP119 family.
--
-- Once those two implications are supplied, continuum OS0/OS5 are compiler
-- consequences.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as OS05
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record MarkedMomentOS05Inputs
    (Configuration Polymer Observable : Set)
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
    (model : FP.AbstractPolymerModel Polymer)
    (marked : FP.MarkedActivityData Polymer Observable model)
    (moments : Physical.MarkedMomentClosure Polymer Observable model marked)
    : Set₂ where
  field
    FiniteRegularity :
      OS05.ExpectationFunctional Configuration → Set
    ContinuumRegularity :
      OS05.ExpectationFunctional Configuration → Set

    FiniteGrowthControl :
      OS05.ExpectationFunctional Configuration → Set
    ContinuumGrowthControl :
      OS05.ExpectationFunctional Configuration → Set

    -- Exact analytic/semantic transport still required:
    -- the already-selected marked moment theorem must imply the chosen finite
    -- REAL CMP119 OS predicates.
    markedMomentsImplyFiniteRegularity :
      ∀ cutoff →
      FiniteRegularity (Limit.finiteExpectation family cutoff)

    markedMomentsImplyFiniteGrowth :
      ∀ cutoff →
      FiniteGrowthControl (Limit.finiteExpectation family cutoff)

    regularityClosedUnderCanonicalLimit :
      (∀ cutoff →
        FiniteRegularity (Limit.finiteExpectation family cutoff)) →
      ContinuumRegularity (Limit.limitExpectation family)

    growthClosedUnderCanonicalLimit :
      (∀ cutoff →
        FiniteGrowthControl (Limit.finiteExpectation family cutoff)) →
      ContinuumGrowthControl (Limit.limitExpectation family)

open MarkedMomentOS05Inputs public

asCanonicalOS05 :
  ∀ {Configuration Polymer Observable
      sequenceLimit limitLaws quotient division family model marked moments} →
  MarkedMomentOS05Inputs
    Configuration Polymer Observable
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family model marked moments →
  OS05.CanonicalCMP119OS05LimitData
    Configuration
    {sequenceLimit}
    {limitLaws}
    {quotient}
    {division}
    family
asCanonicalOS05 inputs = record
  { OS05.CanonicalCMP119OS05LimitData.FiniteRegularity =
      FiniteRegularity inputs
  ; OS05.CanonicalCMP119OS05LimitData.ContinuumRegularity =
      ContinuumRegularity inputs
  ; OS05.CanonicalCMP119OS05LimitData.FiniteGrowthControl =
      FiniteGrowthControl inputs
  ; OS05.CanonicalCMP119OS05LimitData.ContinuumGrowthControl =
      ContinuumGrowthControl inputs
  ; OS05.CanonicalCMP119OS05LimitData.finiteRegularity =
      markedMomentsImplyFiniteRegularity inputs
  ; OS05.CanonicalCMP119OS05LimitData.finiteGrowthControl =
      markedMomentsImplyFiniteGrowth inputs
  ; OS05.CanonicalCMP119OS05LimitData.regularityClosedUnderCanonicalLimit =
      regularityClosedUnderCanonicalLimit inputs
  ; OS05.CanonicalCMP119OS05LimitData.growthClosedUnderCanonicalLimit =
      growthClosedUnderCanonicalLimit inputs
  }

continuumOS0FromMarkedMoments :
  ∀ {Configuration Polymer Observable
      sequenceLimit limitLaws quotient division family model marked moments}
    (inputs :
      MarkedMomentOS05Inputs
        Configuration Polymer Observable
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family model marked moments) →
  ContinuumRegularity inputs (Limit.limitExpectation family)
continuumOS0FromMarkedMoments inputs =
  OS05.canonicalCMP119OS0 (asCanonicalOS05 inputs)

continuumOS5FromMarkedMoments :
  ∀ {Configuration Polymer Observable
      sequenceLimit limitLaws quotient division family model marked moments}
    (inputs :
      MarkedMomentOS05Inputs
        Configuration Polymer Observable
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family model marked moments) →
  ContinuumGrowthControl inputs (Limit.limitExpectation family)
continuumOS5FromMarkedMoments inputs =
  OS05.canonicalCMP119OS5 (asCanonicalOS05 inputs)

round446MarkedMomentOS05CompilerLevel : ProofLevel
round446MarkedMomentOS05CompilerLevel = machineChecked

round446MarkedFPToRealFiniteOS05MeaningLevel : ProofLevel
round446MarkedFPToRealFiniteOS05MeaningLevel = conditional

round446RealT5MomentProducerRequired : Bool
round446RealT5MomentProducerRequired = false

round446IndependentContinuumOS05TheoremRequired : Bool
round446IndependentContinuumOS05TheoremRequired = false
