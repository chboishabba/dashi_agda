{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayMomentOS05MaxCutRound500Exact where

------------------------------------------------------------------------
-- GOAL-1 A4/A5 / ROUND500: EXACT FINITE OS0/OS5 MAX-CUT
--
-- R464's single conditional label contains three logically distinct physical
-- payments:
--
--   O1 the quantitative T5 producer is attached to the SAME literal CMP119
--      finite expectation family;
--   O2 its quantitative bounds imply the chosen finite OS0/regularity predicate;
--   O3 its quantitative bounds imply the chosen finite OS5/growth predicate.
--
-- The continuum closure of O2/O3 is standard/compiler-owned by R464/OS05.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

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
import DASHI.Physics.YangMills.YangMillsClayT5MomentToOS05Round464Exact as R464

record MomentOS05SourceInputs
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

    quantitativeFiniteExpectationIsCMP119 :
      ∀ cutoff observable →
      Gram.expectation
        (T5.operations (T5.thermodynamic quantitative))
        (T5.diagonalMeasure quantitative cutoff)
        observable
      ≡
      Limit.finiteExpectation family cutoff observable

    FiniteRegularity :
      OS05.ExpectationFunctional Configuration → Set
    ContinuumRegularity :
      OS05.ExpectationFunctional Configuration → Set
    FiniteGrowthControl :
      OS05.ExpectationFunctional Configuration → Set
    ContinuumGrowthControl :
      OS05.ExpectationFunctional Configuration → Set

    quantitativeBoundsImplyFiniteRegularity :
      ∀ cutoff →
      FiniteRegularity (Limit.finiteExpectation family cutoff)

    quantitativeBoundsImplyFiniteGrowth :
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

open MomentOS05SourceInputs public

asRound464 :
  ∀ {Configuration Measure sequenceLimit limitLaws quotient division family} →
  MomentOS05SourceInputs
    Configuration Measure
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family →
  R464.QuantitativeMomentOS05Bridge
    Configuration Measure
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family
asRound464 inputs = record
  { R464.QuantitativeMomentOS05Bridge.quantitative =
      quantitative inputs
  ; R464.QuantitativeMomentOS05Bridge.quantitativeFiniteExpectationIsCMP119 =
      quantitativeFiniteExpectationIsCMP119 inputs
  ; R464.QuantitativeMomentOS05Bridge.FiniteRegularity =
      FiniteRegularity inputs
  ; R464.QuantitativeMomentOS05Bridge.ContinuumRegularity =
      ContinuumRegularity inputs
  ; R464.QuantitativeMomentOS05Bridge.FiniteGrowthControl =
      FiniteGrowthControl inputs
  ; R464.QuantitativeMomentOS05Bridge.ContinuumGrowthControl =
      ContinuumGrowthControl inputs
  ; R464.QuantitativeMomentOS05Bridge.quantitativeBoundsImplyFiniteRegularity =
      quantitativeBoundsImplyFiniteRegularity inputs
  ; R464.QuantitativeMomentOS05Bridge.quantitativeBoundsImplyFiniteGrowth =
      quantitativeBoundsImplyFiniteGrowth inputs
  ; R464.QuantitativeMomentOS05Bridge.regularityClosedUnderCanonicalLimit =
      regularityClosedUnderCanonicalLimit inputs
  ; R464.QuantitativeMomentOS05Bridge.growthClosedUnderCanonicalLimit =
      growthClosedUnderCanonicalLimit inputs
  }

round500OS05CompilerLevel : ProofLevel
round500OS05CompilerLevel = machineChecked

round500ContinuumClosureAuthorityLevel : ProofLevel
round500ContinuumClosureAuthorityLevel =
  R464.round464OS05ClosureAuthorityLevel

literalRound500QuantitativeFiniteExpectationAttachmentLevel : ProofLevel
literalRound500QuantitativeFiniteExpectationAttachmentLevel = conditional

literalRound500FiniteRegularityFromQuantitativeBoundsLevel : ProofLevel
literalRound500FiniteRegularityFromQuantitativeBoundsLevel = conditional

literalRound500FiniteGrowthFromQuantitativeBoundsLevel : ProofLevel
literalRound500FiniteGrowthFromQuantitativeBoundsLevel = conditional
