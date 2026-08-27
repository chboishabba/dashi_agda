module DASHI.Foundations.Wette1969FiniteDerivationContextExact where

------------------------------------------------------------------------
-- WETTE 1969 FINITE DERIVATION CONTEXT / CERTIFIED TRACE ERASURE
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Repo-native consolidation:
--   * TypedDependencyCore / ProofCarryingRuleApplicationExact own admissible
--     proof-carrying actions;
--   * WetteFiniteDeductionTraceExact already owns mixed-generator finite runs;
--   * this module instantiates the previously abstract HistoricalContextSystem
--     by a finite monotone list of formulae and proves that certified historical
--     traces erase to the existing Wette finite-trace semantics.
--
-- This is an operational derivation-context model only. Membership in the
-- context means "already available in this finite derivation state"; it is not
-- a semantic truth predicate and does not discharge Wette's Hauptsaetze.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.WetteConstructiveAutomatonExact as Automaton
import DASHI.Foundations.WetteFiniteDeductionTraceExact as Trace

------------------------------------------------------------------------
-- Finite monotone formula contexts.
------------------------------------------------------------------------

DerivationContext : Set
DerivationContext = List Signature.Formula

data _∈Context_ (formula : Signature.Formula) : DerivationContext → Set where
  here : ∀ {rest} → formula ∈Context (formula ∷ rest)
  there : ∀ {head rest} → formula ∈Context rest → formula ∈Context (head ∷ rest)

finiteHistoricalContextSystem : Historical.HistoricalContextSystem
finiteHistoricalContextSystem =
  Historical.historicalContextSystem
    DerivationContext
    (λ context formula → formula ∈Context context)
    (λ context formula → formula ∷ context)

newConclusionAvailable :
  (context : DerivationContext) →
  (formula : Signature.Formula) →
  Historical.Derives finiteHistoricalContextSystem
    (Historical.extend finiteHistoricalContextSystem context formula)
    formula
newConclusionAvailable context formula = here

oldFormulaRemainsAvailable :
  (context : DerivationContext) →
  (new formula : Signature.Formula) →
  Historical.Derives finiteHistoricalContextSystem context formula →
  Historical.Derives finiteHistoricalContextSystem
    (Historical.extend finiteHistoricalContextSystem context new)
    formula
oldFormulaRemainsAvailable context new formula evidence = there evidence

------------------------------------------------------------------------
-- Existing WetteMachineSpec / finite trace instance.
--
-- Generator = historical rule body.
-- State     = finite derivation context.
-- Step      = prepend the rule conclusion.
--
-- The Bool-valued WetteMachineSpec `admissible` field is intentionally trivial
-- here because actual rule legality lives in the proof-relevant
-- TypedDependencyCore precondition. This prevents Bool from becoming a second
-- competing admissibility authority.
------------------------------------------------------------------------

finiteContextMachine : Automaton.WetteMachineSpec
finiteContextMachine = record
  { State = DerivationContext
  ; Generator = RuleBody.HistoricalRuleBody
  ; admissible = λ context → true
  ; step = λ rule context → RuleBody.conclusion rule ∷ context
  ; preservesAdmissible = λ rule context admissible → refl
  }

finiteContextSimulation : Automaton.WetteDeductionSimulation finiteContextMachine
finiteContextSimulation = record
  { Syntax = DerivationContext
  ; encode = λ context → context
  ; syntaxStep = λ rule context → RuleBody.conclusion rule ∷ context
  ; stepCommutes = λ rule context → refl
  }

------------------------------------------------------------------------
-- Forget proof witnesses, retain only the historical generator sequence.
------------------------------------------------------------------------

eraseCertifiedRules :
  {context : DerivationContext} →
  PCRA.CertifiedRuleTrace
    (Historical.historicalRuleApplicationSystem finiteHistoricalContextSystem)
    context →
  List RuleBody.HistoricalRuleBody
eraseCertifiedRules PCRA.done = []
eraseCertifiedRules (PCRA.choose selected rest) =
  PCRA.selectedRule selected ∷ eraseCertifiedRules rest

------------------------------------------------------------------------
-- Run congruence for the existing finite-trace owner.
------------------------------------------------------------------------

runFiniteContextCong :
  (rules : List RuleBody.HistoricalRuleBody) →
  {left right : DerivationContext} →
  left ≡ right →
  Trace.runSyntax finiteContextSimulation rules left
    ≡ Trace.runSyntax finiteContextSimulation rules right
runFiniteContextCong rules refl = refl

------------------------------------------------------------------------
-- Certified dependent trace -> existing mixed-generator finite trace.
--
-- The only non-definitional seam is exactly the TypedDependencyCore
-- postcondition carried by each selected action: its reached state is proved to
-- be extension by the historical conclusion. That proof transports the
-- induction hypothesis onto the ordinary list-run state.
------------------------------------------------------------------------

certifiedTraceErasesToFiniteRun :
  {context : DerivationContext} →
  (trace :
    PCRA.CertifiedRuleTrace
      (Historical.historicalRuleApplicationSystem finiteHistoricalContextSystem)
      context) →
  Trace.runSyntax finiteContextSimulation (eraseCertifiedRules trace) context
    ≡ PCRA.runCertifiedTrace
        (Historical.historicalRuleApplicationSystem finiteHistoricalContextSystem)
        trace
certifiedTraceErasesToFiniteRun PCRA.done = refl
certifiedTraceErasesToFiniteRun
  {context}
  (PCRA.choose selected rest) =
  trans
    (runFiniteContextCong
      (eraseCertifiedRules rest)
      (sym
        (Dependency.postcondition
          (PCRA.applicationProof selected))))
    (certifiedTraceErasesToFiniteRun rest)

------------------------------------------------------------------------
-- Every certified trace therefore supplies an existing finite derivation
-- witness from its source context to its certified target context.
------------------------------------------------------------------------

certifiedTraceToFiniteDerivationWitness :
  {context : DerivationContext} →
  (trace :
    PCRA.CertifiedRuleTrace
      (Historical.historicalRuleApplicationSystem finiteHistoricalContextSystem)
      context) →
  Trace.FiniteDerivationWitness
    finiteContextSimulation
    context
    (PCRA.runCertifiedTrace
      (Historical.historicalRuleApplicationSystem finiteHistoricalContextSystem)
      trace)
certifiedTraceToFiniteDerivationWitness trace =
  Trace.finiteDerivationWitness
    (eraseCertifiedRules trace)
    (certifiedTraceErasesToFiniteRun trace)

record Wette1969FiniteDerivationContextBoundary : Set where
  constructor wette1969FiniteDerivationContextBoundary
  field
    finiteContextMonotonicallyAccumulatesConclusions : Bool
    finiteContextMonotonicallyAccumulatesConclusionsIsTrue :
      finiteContextMonotonicallyAccumulatesConclusions ≡ true

    proofCarryingTraceErasesToExistingFiniteTrace : Bool
    proofCarryingTraceErasesToExistingFiniteTraceIsTrue :
      proofCarryingTraceErasesToExistingFiniteTrace ≡ true

    certifiedTraceProducesExistingFiniteDerivationWitness : Bool
    certifiedTraceProducesExistingFiniteDerivationWitnessIsTrue :
      certifiedTraceProducesExistingFiniteDerivationWitness ≡ true

    boolMachineAdmissibilityIsHistoricalRuleAuthority : Bool
    boolMachineAdmissibilityIsHistoricalRuleAuthorityIsFalse :
      boolMachineAdmissibilityIsHistoricalRuleAuthority ≡ false

    finiteContextMembershipIsAlreadySemanticTruth : Bool
    finiteContextMembershipIsAlreadySemanticTruthIsFalse :
      finiteContextMembershipIsAlreadySemanticTruth ≡ false

canonicalWette1969FiniteDerivationContextBoundary :
  Wette1969FiniteDerivationContextBoundary
canonicalWette1969FiniteDerivationContextBoundary =
  wette1969FiniteDerivationContextBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
