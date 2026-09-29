{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayRepresentedOS05Round481Exact where

------------------------------------------------------------------------
-- GOAL-1 A4/A5 / ROUND481:
-- TRANSPORT CANONICAL OS0/OS5 TO THE REPRESENTED CONTINUUM
--
-- R464 proves OS0/OS5 on the selected canonical expectation limit.  R476 says
-- that the same source limit is represented by integration against an actual
-- countably-additive measure.  For predicates extensional under pointwise
-- expectation equality, transport is compiler work rather than a new moment or
-- OS theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayT5MomentToOS05Round464Exact as R464
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

ExpectationFunctional : Set → Set
ExpectationFunctional Configuration =
  (Configuration → ℝ) → ℝ

record ExtensionalPredicate
    {Configuration : Set}
    (Predicate : ExpectationFunctional Configuration → Set)
    : Set₁ where
  field
    transport :
      ∀ left right →
      (∀ observable → left observable ≡ right observable) →
      Predicate left →
      Predicate right

open ExtensionalPredicate public

representedExpectation :
  ∀ {Configuration}
    (represented :
      R476.RepresentedContinuum (Configuration → ℝ)) →
  ExpectationFunctional Configuration
representedExpectation represented =
  λ observable →
    R476.integrate represented (R476.measure represented) observable

record RepresentedOS05
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
    (bridge :
      R464.QuantitativeMomentOS05Bridge
        Configuration Measure
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family)
    : Set₂ where
  field
    representation :
      R476.SourceLimitRepresentation
        (Configuration → ℝ)
        (Limit.limitExpectation family)

    regularityExtensional :
      ExtensionalPredicate
        (R464.ContinuumRegularity bridge)

    growthExtensional :
      ExtensionalPredicate
        (R464.ContinuumGrowthControl bridge)

open RepresentedOS05 public

limitEqualsRepresentedExpectation :
  ∀ {Configuration Measure sequenceLimit limitLaws quotient division
      family bridge}
    (dataSet :
      RepresentedOS05
        Configuration Measure
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family bridge)
    observable →
  Limit.limitExpectation family observable
  ≡ representedExpectation
      (R476.represented (representation dataSet))
      observable
limitEqualsRepresentedExpectation dataSet observable =
  R476.sourceLimitIsIntegral (representation dataSet) observable

representedOS0 :
  ∀ {Configuration Measure sequenceLimit limitLaws quotient division
      family bridge}
    (dataSet :
      RepresentedOS05
        Configuration Measure
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family bridge) →
  R464.ContinuumRegularity bridge
    (representedExpectation
      (R476.represented (representation dataSet)))
representedOS0 {family = family} {bridge = bridge} dataSet =
  transport (regularityExtensional dataSet)
    (Limit.limitExpectation family)
    (representedExpectation
      (R476.represented (representation dataSet)))
    (limitEqualsRepresentedExpectation dataSet)
    (R464.continuumOS0FromQuantitativeMoments bridge)

representedOS5 :
  ∀ {Configuration Measure sequenceLimit limitLaws quotient division
      family bridge}
    (dataSet :
      RepresentedOS05
        Configuration Measure
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family bridge) →
  R464.ContinuumGrowthControl bridge
    (representedExpectation
      (R476.represented (representation dataSet)))
representedOS5 {family = family} {bridge = bridge} dataSet =
  transport (growthExtensional dataSet)
    (Limit.limitExpectation family)
    (representedExpectation
      (R476.represented (representation dataSet)))
    (limitEqualsRepresentedExpectation dataSet)
    (R464.continuumOS5FromQuantitativeMoments bridge)

newMomentEstimateRequired : Bool
newMomentEstimateRequired = false

wholeMeasureRecordEqualityRequired : Bool
wholeMeasureRecordEqualityRequired = false

round481RepresentedOS05CompilerLevel : ProofLevel
round481RepresentedOS05CompilerLevel = machineChecked

literalRound481ExtensionalOSMeaningLevel : ProofLevel
literalRound481ExtensionalOSMeaningLevel = conditional
