module DASHI.Foundations.Wette1969CertifiedFormulaProducerExact where

------------------------------------------------------------------------
-- CERTIFIED HISTORICAL FORMULA PRODUCERS
--
-- A producer is stronger than a bare membership hypothesis: it carries an
-- actual proof-carrying historical trace whose target context contains the
-- requested formula.  This is the reusable interface for the 9.1.5 syntactic
-- scaffold.  Atomic freshness/formation receipts may seed producers, while
-- structural J/8.3/7/8.2/10 rules extend them.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Formula = Signature.Formula
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record CertifiedFormulaProducer
    (initial : Context)
    (formula : Formula) : Set₁ where
  constructor certifiedFormulaProducer
  field
    trace : PCRA.CertifiedRuleTrace historicalSystem initial
    produced :
      formula Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem trace)

open CertifiedFormulaProducer public

producerTarget :
  {initial : Context} → {formula : Formula} →
  CertifiedFormulaProducer initial formula → Context
producerTarget producer =
  PCRA.runCertifiedTrace historicalSystem (trace producer)

atomicReceiptProducer :
  {context : Context} → {formula : Formula} →
  formula Finite.∈Context context →
  CertifiedFormulaProducer context formula
atomicReceiptProducer evidence =
  certifiedFormulaProducer PCRA.done evidence

transportProducedAcrossTrace :
  {initial : Context} → {formula : Formula} →
  (producer : CertifiedFormulaProducer initial formula) →
  (tail : PCRA.CertifiedRuleTrace historicalSystem (producerTarget producer)) →
  formula Finite.∈Context
    (PCRA.runCertifiedTrace historicalSystem tail)
transportProducedAcrossTrace producer tail =
  Closure.certifiedTracePreservesPriorFormula tail _ (produced producer)

appendProducerTrace :
  {initial : Context} → {formula : Formula} →
  (producer : CertifiedFormulaProducer initial formula) →
  (tail : PCRA.CertifiedRuleTrace historicalSystem (producerTarget producer)) →
  CertifiedFormulaProducer initial formula
appendProducerTrace producer tail =
  certifiedFormulaProducer
    (PCRA.appendCertifiedTrace (trace producer) tail)
    (transportProducedAcrossTrace producer tail)

record Wette1969CertifiedFormulaProducerBoundary : Set where
  constructor wette1969CertifiedFormulaProducerBoundary
  field
    producerCarriesHistoricalTrace : Bool
    producerCarriesHistoricalTraceIsTrue : producerCarriesHistoricalTrace ≡ true
    producerCarriesTargetMembershipReceipt : Bool
    producerCarriesTargetMembershipReceiptIsTrue :
      producerCarriesTargetMembershipReceipt ≡ true
    atomicReceiptMaySeedButDoesNotManufactureFreshness : Bool
    atomicReceiptMaySeedButDoesNotManufactureFreshnessIsTrue :
      atomicReceiptMaySeedButDoesNotManufactureFreshness ≡ true

canonicalWette1969CertifiedFormulaProducerBoundary :
  Wette1969CertifiedFormulaProducerBoundary
canonicalWette1969CertifiedFormulaProducerBoundary =
  wette1969CertifiedFormulaProducerBoundary true refl true refl true refl
