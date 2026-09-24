{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayT5QuantitativeContinuumMaxCutRound443Exact where

------------------------------------------------------------------------
-- ROUND443 / ONE QUANTITATIVE T5 OBJECT FEEDS H2 EXISTENCE FALLBACK + OS0/OS5
--
-- Clay-facing scheduling point:
--
--   the finite quantitative estimate used for global compact containment and
--   the finite quantitative estimate used for OS0/OS5 must live on the SAME
--   literal CMP119/T5 expectation producer.
--
-- This owner does not assert either analytic theorem.  It prevents the proof
-- graph from paying them on unrelated finite families and exposes the genuine
-- shared max-cut object.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as Containment
import DASHI.Physics.YangMills.BalabanClayT5BoundedWeakCompactnessRound439Exact as R439
import DASHI.Physics.YangMills.YangMillsClayT5MomentToOS05Round464Exact as R464
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record QuantitativeContinuumMaxCut
    (Configuration Measure Epsilon Witness : Set)
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

    -- One same-family attachment for BOTH continuum consumers.
    finiteExpectationIsCMP119 :
      ∀ cutoff observable →
      DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact.expectation
        (T5.operations (T5.thermodynamic quantitative))
        (T5.diagonalMeasure quantitative cutoff)
        observable
      ≡
      Limit.finiteExpectation family cutoff observable

    -- H2 existence fallback: the actual global compact-containment theorem.
    globalContainment :
      Containment.SelectedMomentCompactContainmentInputs
        Measure (Configuration → ℝ) ℝ Epsilon Witness quantitative

    -- A4/A5: the SAME quantitative producer pays the selected finite
    -- regularity/growth predicates.
    os05 :
      R464.QuantitativeMomentOS05Bridge
        Configuration Measure family

    os05UsesSameQuantitativeProducer :
      R464.quantitative os05 ≡ quantitative

open QuantitativeContinuumMaxCut public

continuumOS0 :
  ∀ {Configuration Measure Epsilon Witness
      sequenceLimit limitLaws quotient division family}
    (dataSet :
      QuantitativeContinuumMaxCut
        Configuration Measure Epsilon Witness
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family) →
  R464.ContinuumRegularity (os05 dataSet)
    (Limit.limitExpectation family)
continuumOS0 dataSet =
  R464.continuumOS0FromQuantitativeMoments (os05 dataSet)

continuumOS5 :
  ∀ {Configuration Measure Epsilon Witness
      sequenceLimit limitLaws quotient division family}
    (dataSet :
      QuantitativeContinuumMaxCut
        Configuration Measure Epsilon Witness
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family) →
  R464.ContinuumGrowthControl (os05 dataSet)
    (Limit.limitExpectation family)
continuumOS5 dataSet =
  R464.continuumOS5FromQuantitativeMoments (os05 dataSet)

round443SameQuantitativeFamilyCompilerLevel : ProofLevel
round443SameQuantitativeFamilyCompilerLevel = machineChecked

round443GlobalCompactContainmentLevel : ProofLevel
round443GlobalCompactContainmentLevel = conditional

round443FiniteOS0OS5QuantitativeMeaningLevel : ProofLevel
round443FiniteOS0OS5QuantitativeMeaningLevel = conditional

round443SeparateMomentPackagesForCompactnessAndOS05Required : Bool
round443SeparateMomentPackagesForCompactnessAndOS05Required = false
