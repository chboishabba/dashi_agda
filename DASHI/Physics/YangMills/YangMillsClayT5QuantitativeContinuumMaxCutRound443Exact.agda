{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayT5QuantitativeContinuumMaxCutRound443Exact where

------------------------------------------------------------------------
-- ROUND443 / ONE MARKED-FP MOMENT OBJECT FEEDS COMPACTNESS + OS0/OS5
--
-- The source-native quantitative max-cut is not one scalar carrier:
--
--   * the mature marked-polymer moment theorem is rational-valued;
--   * the canonical literal CMP119 OS0/OS5 family is real-valued.
--
-- The correct same-family invariant is therefore the SAME MarkedMomentClosure,
-- not equality of rational and real producer records.
--
-- One marked closure feeds:
--
--   R444/R445 -> selected rational T5 moment producer -> compact containment
--   R446      -> finite real CMP119 OS0/OS5 semantics -> continuum OS0/OS5.
--
-- Cross-carrier physical meaning remains explicit inside R446; no record
-- extensionality or fictitious real T5 moment producer is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as Containment
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP
import DASHI.Physics.YangMills.BalabanClayT5MarkedPreferredExpectationRound445Exact as R445
import DASHI.Physics.YangMills.BalabanClayT5MarkedMomentOS05Round446Exact as R446
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record QuantitativeContinuumMaxCut
    (Configuration Measure Observable Polymer Epsilon Witness : Set)
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
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData Measure Observable ℚ)
    (model : FP.AbstractPolymerModel Polymer)
    (marked : FP.MarkedActivityData Polymer Observable model)
    (moments : Physical.MarkedMomentClosure Polymer Observable model marked)
    : Set₂ where
  field
    -- Rational selected-expectation realization of THIS marked closure.
    preferredExpectation :
      R445.MarkedPreferredExpectationInputs
        thermodynamic model marked moments

    -- H2 existence fallback consumes the exact selected producer generated from
    -- that same marked closure.
    globalContainment :
      Containment.SelectedMomentCompactContainmentInputs
        Measure Observable ℚ Epsilon Witness
        (R445.compileMarkedPreferredExpectationProducer preferredExpectation)

    -- A4/A5 consumes the SAME marked closure on the literal real CMP119 family.
    os05 :
      R446.MarkedMomentOS05Inputs
        Configuration Polymer Observable
        family model marked moments

open QuantitativeContinuumMaxCut public

continuumOS0 :
  ∀ {Configuration Measure Observable Polymer Epsilon Witness
      sequenceLimit limitLaws quotient division family thermodynamic
      model marked moments}
    (dataSet :
      QuantitativeContinuumMaxCut
        Configuration Measure Observable Polymer Epsilon Witness
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family thermodynamic model marked moments) →
  R446.ContinuumRegularity (os05 dataSet)
    (Limit.limitExpectation family)
continuumOS0 dataSet =
  R446.continuumOS0FromMarkedMoments (os05 dataSet)

continuumOS5 :
  ∀ {Configuration Measure Observable Polymer Epsilon Witness
      sequenceLimit limitLaws quotient division family thermodynamic
      model marked moments}
    (dataSet :
      QuantitativeContinuumMaxCut
        Configuration Measure Observable Polymer Epsilon Witness
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family thermodynamic model marked moments) →
  R446.ContinuumGrowthControl (os05 dataSet)
    (Limit.limitExpectation family)
continuumOS5 dataSet =
  R446.continuumOS5FromMarkedMoments (os05 dataSet)

round443SameMarkedMomentSourceCompilerLevel : ProofLevel
round443SameMarkedMomentSourceCompilerLevel = machineChecked

round443GlobalCompactContainmentLevel : ProofLevel
round443GlobalCompactContainmentLevel = conditional

round443MarkedFPToRealFiniteOS05MeaningLevel : ProofLevel
round443MarkedFPToRealFiniteOS05MeaningLevel = conditional

round443LiteralCMP119TypedMomentRealizationLevel : ProofLevel
round443LiteralCMP119TypedMomentRealizationLevel = conditional

round443SeparateMomentPackagesForCompactnessAndOS05Required : Bool
round443SeparateMomentPackagesForCompactnessAndOS05Required = false

round443RealT5MomentProducerRequired : Bool
round443RealT5MomentProducerRequired = false
