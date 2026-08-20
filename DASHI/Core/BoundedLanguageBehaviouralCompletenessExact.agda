module DASHI.Core.BoundedLanguageBehaviouralCompletenessExact where

------------------------------------------------------------------------
-- BOUNDED LANGUAGE COMPLETENESS != BEAM TERMINATION
--
-- The cross-domain requirement is exact and deliberately modest: exhaustion is
-- always relative to a declared finite action language / horizon.  SeaMeInIt
-- operator search, Animalexic hypothesis/intervention grammars and LES planning
-- may all use this theorem surface without promoting finite bounded coverage to
-- global continuous-state optimality.
--
-- Literature calibration:
-- Robert Paige and Robert E. Tarjan,
-- "Three Partition Refinement Algorithms", SIAM Journal on Computing 16(6),
-- 1987. DOI: 10.1137/0216062.
-- Thomas Dean and Robert Givan, "Model Minimization in Markov Decision
-- Processes", AAAI 1997.  No DOI is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Membership.Propositional using (_∈_)

import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed

------------------------------------------------------------------------
-- A finite action list is complete only relative to the consumer's declared
-- action predicate.  The list itself is not evidence of completeness.
------------------------------------------------------------------------

record FiniteDeclaredActionLanguage
    {State Action Consumer Observation : Set}
    (system : Governed.ConsumerIndexedGovernedTransition
      State Action Consumer Observation)
    (consumer : Consumer) : Set₁ where
  constructor finiteDeclaredActionLanguage
  field
    actions : List Action
    languageReference : String
    complete :
      ∀ action →
      Governed.declaredAction system consumer action →
      action ∈ actions

open FiniteDeclaredActionLanguage public

------------------------------------------------------------------------
-- Consumer-specific stabilization of the bounded behavioural relation.
------------------------------------------------------------------------

record ConsumerStableAt
    {State Action Consumer Observation : Set}
    (system : Governed.ConsumerIndexedGovernedTransition
      State Action Consumer Observation)
    (consumer : Consumer)
    (depth : Nat) : Set₁ where
  constructor consumerStableAt
  field
    forwardStable :
      ∀ {left right} →
      Governed.FutureEquivalent system consumer depth left right →
      Governed.FutureEquivalent system consumer (suc depth) left right

open ConsumerStableAt public

stabilizedPairSurvivesOneMoreDepth :
  ∀ {State Action Consumer Observation}
    {system : Governed.ConsumerIndexedGovernedTransition
      State Action Consumer Observation}
    {consumer : Consumer}
    {depth : Nat}
    (stable : ConsumerStableAt system consumer depth)
    {left right : State} →
  Governed.FutureEquivalent system consumer depth left right →
  Governed.FutureEquivalent system consumer (suc depth) left right
stabilizedPairSurvivesOneMoreDepth stable related =
  forwardStable stable related

------------------------------------------------------------------------
-- The positive certificate binds language coverage and behavioural stability.
-- A runtime receipt can additionally bind backend/policy/dedup hashes, but
-- those are implementation provenance rather than a theorem premise here.
------------------------------------------------------------------------

record LanguageRelativeBehaviouralExhaustion
    {State Action Consumer Observation : Set}
    (system : Governed.ConsumerIndexedGovernedTransition
      State Action Consumer Observation)
    (consumer : Consumer) : Set₁ where
  constructor languageRelativeBehaviouralExhaustion
  field
    language : FiniteDeclaredActionLanguage system consumer
    depth : Nat
    stable : ConsumerStableAt system consumer depth
    stateDomainReference : String
    backendReference : String
    policyReference : String
    dedupReference : String

open LanguageRelativeBehaviouralExhaustion public

certificateGivesStableStep :
  ∀ {State Action Consumer Observation}
    {system : Governed.ConsumerIndexedGovernedTransition
      State Action Consumer Observation}
    {consumer : Consumer}
    (certificate : LanguageRelativeBehaviouralExhaustion system consumer)
    {left right : State} →
  Governed.FutureEquivalent system consumer (depth certificate) left right →
  Governed.FutureEquivalent system consumer (suc (depth certificate)) left right
certificateGivesStableStep certificate =
  forwardStable (stable certificate)

------------------------------------------------------------------------
-- Negative boundary: a stopped beam is a different object.  There is no
-- constructor from BeamTermination to LanguageRelativeBehaviouralExhaustion.
------------------------------------------------------------------------

record BeamTermination : Set where
  constructor beamTermination
  field
    beamWidth : Nat
    searchDepth : Nat
    noRetainedChild : Bool
    heuristicReference : String

open BeamTermination public

record BoundedLanguageBoundary : Set where
  constructor boundedLanguageBoundary
  field
    beamTerminationIsNotBehaviouralStability : Bool
    finiteCoverageIsRelativeToDeclaredGrammar : Bool
    finiteStabilityDoesNotProveContinuousGlobalOptimality : Bool
    backendPolicyAndDedupArePartOfClaimScope : Bool

canonicalBoundedLanguageBoundary : BoundedLanguageBoundary
canonicalBoundedLanguageBoundary =
  boundedLanguageBoundary true true true true
