module DASHI.Foundations.Wette1969CertifiedHistoricalConclusionProducerExact where

------------------------------------------------------------------------
-- CERTIFIED HISTORICAL CONCLUSION PRODUCER
--
-- `CertifiedFormulaProducer` permits an atomic receipt to seed a producer.  For
-- the 9.1.5 scaffold we need the stronger statement that a requested formula is
-- actually the conclusion of a certified historical rule application somewhere
-- in the trace.  This record isolates that stronger notion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Formula = Signature.Formula
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record CertifiedHistoricalConclusionProducer
    (initial : Context)
    (formula : Formula) : Set₁ where
  constructor certifiedHistoricalConclusionProducer
  field
    prefix : PCRA.CertifiedRuleTrace historicalSystem initial
    selected :
      PCRA.SelectedRuleApplication historicalSystem
        (PCRA.runCertifiedTrace historicalSystem prefix)
    conclusionMatches :
      RuleBody.conclusion (PCRA.selectedRule selected) ≡ formula
    suffix :
      PCRA.CertifiedRuleTrace historicalSystem
        (PCRA.applySelected historicalSystem selected)

open CertifiedHistoricalConclusionProducer public

producerTrace :
  {initial : Context} → {formula : Formula} →
  CertifiedHistoricalConclusionProducer initial formula →
  PCRA.CertifiedRuleTrace historicalSystem initial
producerTrace producer =
  PCRA.appendCertifiedTrace
    (prefix producer)
    (PCRA.choose (selected producer) (suffix producer))

producerTarget :
  {initial : Context} → {formula : Formula} →
  CertifiedHistoricalConclusionProducer initial formula → Context
producerTarget producer =
  PCRA.runCertifiedTrace historicalSystem (suffix producer)

producedAtTarget :
  {initial : Context} → {formula : Formula} →
  (producer : CertifiedHistoricalConclusionProducer initial formula) →
  formula Finite.∈Context (producerTarget producer)
producedAtTarget producer
  rewrite sym (conclusionMatches producer) =
  Closure.headConclusionAvailableAtTraceTarget
    (selected producer)
    (suffix producer)

singleStepProducer :
  {context : Context} → {formula : Formula} →
  (selected : PCRA.SelectedRuleApplication historicalSystem context) →
  RuleBody.conclusion (PCRA.selectedRule selected) ≡ formula →
  CertifiedHistoricalConclusionProducer context formula
singleStepProducer selected equality =
  certifiedHistoricalConclusionProducer
    PCRA.done selected equality PCRA.done

transportProducerTargetEvidence :
  {initial : Context} → {formula : Formula} →
  (producer : CertifiedHistoricalConclusionProducer initial formula) →
  (tail : PCRA.CertifiedRuleTrace historicalSystem (producerTarget producer)) →
  formula Finite.∈Context (PCRA.runCertifiedTrace historicalSystem tail)
transportProducerTargetEvidence producer tail =
  Closure.certifiedTracePreservesPriorFormula
    tail formula (producedAtTarget producer)

record Wette1969CertifiedHistoricalConclusionProducerBoundary : Set where
  constructor wette1969CertifiedHistoricalConclusionProducerBoundary
  field
    producerContainsActualSelectedHistoricalRule : Bool
    producerContainsActualSelectedHistoricalRuleIsTrue :
      producerContainsActualSelectedHistoricalRule ≡ true
    requestedFormulaMustEqualSelectedRuleConclusion : Bool
    requestedFormulaMustEqualSelectedRuleConclusionIsTrue :
      requestedFormulaMustEqualSelectedRuleConclusion ≡ true
    bareInitialMembershipCannotByItselfSatisfyThisProducer : Bool
    bareInitialMembershipCannotByItselfSatisfyThisProducerIsTrue :
      bareInitialMembershipCannotByItselfSatisfyThisProducer ≡ true

canonicalWette1969CertifiedHistoricalConclusionProducerBoundary :
  Wette1969CertifiedHistoricalConclusionProducerBoundary
canonicalWette1969CertifiedHistoricalConclusionProducerBoundary =
  wette1969CertifiedHistoricalConclusionProducerBoundary
    true refl true refl true refl
