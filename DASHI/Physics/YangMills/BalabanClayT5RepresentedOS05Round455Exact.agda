{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5RepresentedOS05Round455Exact where

------------------------------------------------------------------------
-- ROUND455 / R446 OS0/OS5 -> REPRESENTATION-FIRST CONTINUUM CARRIER
--
-- R446 proves continuum regularity/growth on the selected limit expectation.
-- R450 constructs the literal represented continuum expectation by integration
-- against the countably-additive representing measure.
--
-- Since the two expectation functionals agree pointwise, any OS0/OS5 predicate
-- that is extensional under pointwise equality transports without a new
-- physical estimate and without equality of whole measure records.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5MarkedMomentOS05Round446Exact as R446
import DASHI.Physics.YangMills.YangMillsRepresentedContinuumCarrierRound450Exact as R450
import DASHI.Physics.YangMills.YangMillsRepresentedContinuumTransportRound454Exact as R454
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record RepresentedOS05TransportInputs
    {Configuration Position Polymer Observable : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division}
    {model : FP.AbstractPolymerModel Polymer}
    {marked : FP.MarkedActivityData Polymer Observable model}
    {moments : Physical.MarkedMomentClosure Polymer Observable model marked}
    (os05 :
      R446.MarkedMomentOS05Inputs
        Configuration Polymer Observable
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family model marked moments)
    (carrier :
      R450.RepresentedContinuumCarrier
        Configuration Position
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    : Set₁ where
  field
    regularityExtensional :
      R454.ExtensionalExpectationPredicate
        (R446.ContinuumRegularity os05)

    growthExtensional :
      R454.ExtensionalExpectationPredicate
        (R446.ContinuumGrowthControl os05)

open RepresentedOS05TransportInputs public

representedContinuumOS0 :
  ∀ {Configuration Position Polymer Observable
      sequenceLimit limitLaws quotient division family model marked moments}
    {os05 :
      R446.MarkedMomentOS05Inputs
        Configuration Polymer Observable
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family model marked moments}
    {carrier :
      R450.RepresentedContinuumCarrier
        Configuration Position
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family} →
  RepresentedOS05TransportInputs os05 carrier →
  R446.ContinuumRegularity os05
    (R454.representedExpectation carrier)
representedContinuumOS0 {os05 = os05} {carrier = carrier} inputs =
  R454.transportExpectationPredicate
    (regularityExtensional inputs)
    carrier
    (R446.continuumOS0FromMarkedMoments os05)

representedContinuumOS5 :
  ∀ {Configuration Position Polymer Observable
      sequenceLimit limitLaws quotient division family model marked moments}
    {os05 :
      R446.MarkedMomentOS05Inputs
        Configuration Polymer Observable
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family model marked moments}
    {carrier :
      R450.RepresentedContinuumCarrier
        Configuration Position
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family} →
  RepresentedOS05TransportInputs os05 carrier →
  R446.ContinuumGrowthControl os05
    (R454.representedExpectation carrier)
representedContinuumOS5 {os05 = os05} {carrier = carrier} inputs =
  R454.transportExpectationPredicate
    (growthExtensional inputs)
    carrier
    (R446.continuumOS5FromMarkedMoments os05)

round455RepresentedOS05TransportCompilerLevel : ProofLevel
round455RepresentedOS05TransportCompilerLevel = machineChecked

round455NewPhysicalMomentEstimateRequired : Bool
round455NewPhysicalMomentEstimateRequired = false

round455WholeMeasureEqualityRequired : Bool
round455WholeMeasureEqualityRequired = false
