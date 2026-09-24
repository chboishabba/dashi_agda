{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayT5CoerciveQuantitativeMaxCutRound447Exact where

------------------------------------------------------------------------
-- ROUND447 / ACTUAL QUANTITATIVE MAX-CUT CONSTRUCTOR
--
-- R443 now shares one MarkedMomentClosure across:
--
--   marked moments -> selected T5 moment producer -> compactness lane
--   marked moments -> literal real CMP119 OS0/OS5 lane.
--
-- The compactness field itself should not remain opaque.  Round212 already
-- isolates its exact global physical content:
--
--   selected expectation has probability/Markov semantics,
--   one literal observable is nonnegative and globally coercive,
--   its selected sublevel witnesses are compact/admissible.
--
-- R447 composes that existing theorem with R443.  Therefore no independent
-- tightness / compact-containment theorem remains after these inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5CoerciveMomentMarkovContainmentExact as Coercive
import DASHI.Physics.YangMills.BalabanClayT1SelectedCoerciveContainmentRound212Exact as R212
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP
import DASHI.Physics.YangMills.BalabanClayT5MarkedPreferredExpectationRound445Exact as R445
import DASHI.Physics.YangMills.BalabanClayT5MarkedMomentOS05Round446Exact as R446
import DASHI.Physics.YangMills.YangMillsClayT5QuantitativeContinuumMaxCutRound443Exact as R443
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CoerciveQuantitativeContinuumInputs
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
    preferredExpectation :
      R445.MarkedPreferredExpectationInputs
        thermodynamic model marked moments

    containmentAuthority :
      Coercive.MarkovCompactContainmentAuthority
        Measure Observable ℚ Epsilon Witness

    globalCoercivity :
      R212.SelectedPhysicalCoerciveMomentInputs
        Measure Observable ℚ Epsilon Witness
        (R445.compileMarkedPreferredExpectationProducer preferredExpectation)
        containmentAuthority

    os05 :
      R446.MarkedMomentOS05Inputs
        Configuration Polymer Observable
        family model marked moments

open CoerciveQuantitativeContinuumInputs public

asQuantitativeContinuumMaxCut :
  ∀ {Configuration Measure Observable Polymer Epsilon Witness
      sequenceLimit limitLaws quotient division family thermodynamic
      model marked moments} →
  CoerciveQuantitativeContinuumInputs
    Configuration Measure Observable Polymer Epsilon Witness
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family thermodynamic model marked moments →
  R443.QuantitativeContinuumMaxCut
    Configuration Measure Observable Polymer Epsilon Witness
    family thermodynamic model marked moments
asQuantitativeContinuumMaxCut inputs = record
  { R443.QuantitativeContinuumMaxCut.preferredExpectation =
      preferredExpectation inputs
  ; R443.QuantitativeContinuumMaxCut.globalContainment =
      R212.compileSelectedPhysicalCoerciveContainment
        (globalCoercivity inputs)
  ; R443.QuantitativeContinuumMaxCut.os05 =
      os05 inputs
  }

continuumOS0 :
  ∀ {Configuration Measure Observable Polymer Epsilon Witness
      sequenceLimit limitLaws quotient division family thermodynamic
      model marked moments}
    (inputs :
      CoerciveQuantitativeContinuumInputs
        Configuration Measure Observable Polymer Epsilon Witness
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family thermodynamic model marked moments) →
  R446.ContinuumRegularity (os05 inputs)
    (Limit.limitExpectation family)
continuumOS0 inputs =
  R443.continuumOS0 (asQuantitativeContinuumMaxCut inputs)

continuumOS5 :
  ∀ {Configuration Measure Observable Polymer Epsilon Witness
      sequenceLimit limitLaws quotient division family thermodynamic
      model marked moments}
    (inputs :
      CoerciveQuantitativeContinuumInputs
        Configuration Measure Observable Polymer Epsilon Witness
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family thermodynamic model marked moments) →
  R446.ContinuumGrowthControl (os05 inputs)
    (Limit.limitExpectation family)
continuumOS5 inputs =
  R443.continuumOS5 (asQuantitativeContinuumMaxCut inputs)

round447QuantitativeMaxCutCompilerLevel : ProofLevel
round447QuantitativeMaxCutCompilerLevel = machineChecked

round447IndependentTightnessTheoremRequired : Bool
round447IndependentTightnessTheoremRequired = false

round447MarkedActivitySourceRealizationLevel : ProofLevel
round447MarkedActivitySourceRealizationLevel = conditional

round447GlobalCoercivityCompactSublevelLevel : ProofLevel
round447GlobalCoercivityCompactSublevelLevel = conditional

round447MarkedFPToRealOS05MeaningLevel : ProofLevel
round447MarkedFPToRealOS05MeaningLevel = conditional
