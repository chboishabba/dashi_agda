{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.OptimizationAdmissibilityUnderNondeterminismExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- OPTIMIZATION ADMISSIBILITY UNDER NONDETERMINISTIC SEMANTICS
--
-- The optimization failure exposed by the sparse wildcard lane is generic:
-- one historical implementation trace is not automatically a semantic oracle.
-- A legacy implementation may admit several observationally different outputs
-- for the same input when its internal choice relation is not canonical.
--
-- Therefore the semantic object is a relation of admissible outputs, together
-- with the observation declared by a consumer.  Cost is deliberately absent
-- from this layer.
------------------------------------------------------------------------

record RelationalSpecification
  (Input Output Observation : Set) : Set₁ where
  field
    Admissible : Input → Output → Set
    observe : Output → Observation

open RelationalSpecification public

record ConsumerDeterministic
  {Input Output Observation : Set}
  (specification : RelationalSpecification Input Output Observation) : Set₁ where
  field
    sameObservation :
      ∀ input left right →
      Admissible specification input left →
      Admissible specification input right →
      observe specification left ≡ observe specification right

open ConsumerDeterministic public

------------------------------------------------------------------------
-- An executable implementation is sound only if every selected output belongs
-- to the specification relation.  Soundness alone does NOT make the relation
-- functional and does not turn one execution trace into an oracle.
------------------------------------------------------------------------

record SoundImplementation
  {Input Output Observation : Set}
  (specification : RelationalSpecification Input Output Observation) : Set₁ where
  field
    run : Input → Output
    sound : (input : Input) → Admissible specification input (run input)

open SoundImplementation public

consumerDeterminismMakesAnyTwoSoundImplementationsEquivalent :
  ∀ {Input Output Observation : Set}
    {specification : RelationalSpecification Input Output Observation} →
  ConsumerDeterministic specification →
  (left right : SoundImplementation specification) →
  (input : Input) →
  observe specification (run left input)
    ≡ observe specification (run right input)
consumerDeterminismMakesAnyTwoSoundImplementationsEquivalent deterministic left right input =
  sameObservation deterministic input
    (run left input)
    (run right input)
    (sound left input)
    (sound right input)

------------------------------------------------------------------------
-- TRACE PARITY IS WEAKER THAN SPECIFICATION DETERMINISM
--
-- Equality with one historical legacy trace says only that two chosen runs
-- agree.  It does not prove that all admissible legacy executions agree.
------------------------------------------------------------------------

record TraceParity
  {Input Output Observation : Set}
  (specification : RelationalSpecification Input Output Observation)
  (left right : SoundImplementation specification) : Set₁ where
  field
    agreesOnChosenRuns :
      (input : Input) →
      observe specification (run left input)
        ≡ observe specification (run right input)

open TraceParity public

data TraceParityImpliesConsumerDeterminismPermission : Set where

traceParityCannotManufactureConsumerDeterminism :
  TraceParityImpliesConsumerDeterminismPermission → ⊥
traceParityCannotManufactureConsumerDeterminism ()

------------------------------------------------------------------------
-- DETERMINISING A NONDETERMINISTIC RELATION IS A POLICY REFINEMENT
--
-- A refined relation may discard admissible outputs.  This is consumer-safe
-- only when all discarded and retained choices are observationally equivalent.
------------------------------------------------------------------------

record RelationRefinement
  {Input Output Observation : Set}
  (original refined : RelationalSpecification Input Output Observation) : Set₁ where
  field
    refinedIsOriginal :
      ∀ input output →
      Admissible refined input output →
      Admissible original input output

open RelationRefinement public

record ConsumerConservativeRefinement
  {Input Output Observation : Set}
  {original refined : RelationalSpecification Input Output Observation}
  (refinement : RelationRefinement original refined) : Set₁ where
  field
    eliminatedChoicesAreInvisible :
      ∀ input originalOutput refinedOutput →
      Admissible original input originalOutput →
      Admissible refined input refinedOutput →
      observe original originalOutput ≡ observe refined refinedOutput

open ConsumerConservativeRefinement public

------------------------------------------------------------------------
-- PROCESS CONSTITUTION
--
-- An optimization proposal may proceed to cost comparison only after semantic
-- admissibility has already been established.  There are two legitimate forms:
--
-- 1. the original specification is consumer-deterministic and both old/new
--    implementations are sound;
-- 2. a policy refinement is explicitly declared and separately proved
--    consumer-conservative.
--
-- A benchmark, a historical trace, or an implementation tie-break is not a
-- constructor for either proof.
------------------------------------------------------------------------

data SemanticAdmission
  {Input Output Observation : Set}
  (specification : RelationalSpecification Input Output Observation) : Set₁ where
  deterministicSpecification :
    ConsumerDeterministic specification →
    SemanticAdmission specification

record OptimizationAdmissibility
  (Input Output Observation Cost : Set) : Set₁ where
  field
    specification : RelationalSpecification Input Output Observation
    legacy : SoundImplementation specification
    candidate : SoundImplementation specification
    semanticAdmission : SemanticAdmission specification
    legacyCost : Input → Cost
    candidateCost : Input → Cost

open OptimizationAdmissibility public

semanticParityPrecedesCostComparison :
  ∀ {Input Output Observation Cost : Set}
    (admissibility : OptimizationAdmissibility Input Output Observation Cost) →
    (input : Input) →
  observe (specification admissibility) (run (legacy admissibility) input)
    ≡
  observe (specification admissibility) (run (candidate admissibility) input)
semanticParityPrecedesCostComparison admissibility input
  with semanticAdmission admissibility
... | deterministicSpecification deterministic =
  consumerDeterminismMakesAnyTwoSoundImplementationsEquivalent
    deterministic
    (legacy admissibility)
    (candidate admissibility)
    input

------------------------------------------------------------------------
-- Fail-closed boundary: if consumer determinism is absent and no explicit
-- conservative policy refinement is supplied, optimization has no semantic
-- admission proof regardless of measured runtime.
------------------------------------------------------------------------

data PerformanceEvidence : Set where
  faster : PerformanceEvidence

data PerformanceCanAdmitUnknownSemanticsPermission : Set where

performanceCannotAdmitUnknownSemantics :
  PerformanceEvidence →
  PerformanceCanAdmitUnknownSemanticsPermission →
  ⊥
performanceCannotAdmitUnknownSemantics faster ()
