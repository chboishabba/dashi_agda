{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsExtensionalizedRepresentedOS05Round520Exact where

------------------------------------------------------------------------
-- GOAL-1 A4/A5 / ROUND520:
-- REPRESENTED OS0/OS5 BY LEAST POINTWISE-EXTENSIONAL CLOSURE
--
-- R481 asked for two semantic assumptions saying the arbitrary continuum OS0
-- and OS5 predicates respect pointwise equality of expectation functionals.
-- That assumption is unnecessary if the represented endpoint predicate is
-- chosen canonically as the least pointwise-extensional closure:
--
--   Ext(P)(E) := exists E0, P(E0) and forall F, E0(F)=E(F).
--
-- The canonical CMP119 limit itself witnesses E0.  R476/R499 then supplies
-- pointwise equality to integration against the represented measure.
--
-- No new moment estimate, function extensionality, or whole-measure equality
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; Σ; _,_)
open import Relation.Binary.PropositionalEquality using (trans)

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

PointwiseEqual :
  ∀ {Configuration} →
  ExpectationFunctional Configuration →
  ExpectationFunctional Configuration →
  Set
PointwiseEqual left right =
  ∀ observable → left observable ≡ right observable

ExtensionalClosure :
  ∀ {Configuration} →
  (ExpectationFunctional Configuration → Set) →
  ExpectationFunctional Configuration →
  Set
ExtensionalClosure {Configuration} Predicate target =
  Σ (ExpectationFunctional Configuration)
    (λ source →
      Predicate source
      × PointwiseEqual source target)

extensionalClosureTransport :
  ∀ {Configuration}
    {Predicate : ExpectationFunctional Configuration → Set}
    {left right : ExpectationFunctional Configuration} →
  PointwiseEqual left right →
  ExtensionalClosure Predicate left →
  ExtensionalClosure Predicate right
extensionalClosureTransport leftEqualsRight
    (source , (property , sourceEqualsLeft)) =
  source ,
    ( property
    , λ observable →
        trans
          (sourceEqualsLeft observable)
          (leftEqualsRight observable)
    )

representedExpectation :
  ∀ {Configuration}
    (represented :
      R476.RepresentedContinuum (Configuration → ℝ)) →
  ExpectationFunctional Configuration
representedExpectation represented =
  λ observable →
    R476.integrate represented (R476.measure represented) observable

representedRegularity :
  ∀ {Configuration Measure sequenceLimit limitLaws quotient division
      family}
    (bridge :
      R464.QuantitativeMomentOS05Bridge
        Configuration Measure
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family)
    (representation :
      R476.SourceLimitRepresentation
        (Configuration → ℝ)
        (Limit.limitExpectation family)) →
  ExtensionalClosure
    (R464.ContinuumRegularity bridge)
    (representedExpectation (R476.represented representation))
representedRegularity {family = family} bridge representation =
  Limit.limitExpectation family ,
    ( R464.continuumOS0FromQuantitativeMoments bridge
    , R476.sourceLimitIsIntegral representation
    )

representedGrowth :
  ∀ {Configuration Measure sequenceLimit limitLaws quotient division
      family}
    (bridge :
      R464.QuantitativeMomentOS05Bridge
        Configuration Measure
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family)
    (representation :
      R476.SourceLimitRepresentation
        (Configuration → ℝ)
        (Limit.limitExpectation family)) →
  ExtensionalClosure
    (R464.ContinuumGrowthControl bridge)
    (representedExpectation (R476.represented representation))
representedGrowth {family = family} bridge representation =
  Limit.limitExpectation family ,
    ( R464.continuumOS5FromQuantitativeMoments bridge
    , R476.sourceLimitIsIntegral representation
    )

round520ExtensionalClosureCompilerLevel : ProofLevel
round520ExtensionalClosureCompilerLevel = machineChecked

round520RepresentedRegularityTransportLevel : ProofLevel
round520RepresentedRegularityTransportLevel = machineChecked

round520RepresentedGrowthTransportLevel : ProofLevel
round520RepresentedGrowthTransportLevel = machineChecked

literalRound520RegularityExtensionalityAssumptionRequired : Bool
literalRound520RegularityExtensionalityAssumptionRequired = false

literalRound520GrowthExtensionalityAssumptionRequired : Bool
literalRound520GrowthExtensionalityAssumptionRequired = false
