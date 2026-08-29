module DASHI.Foundations.Wette1969Rule915InductionScaffoldProducerExact where

------------------------------------------------------------------------
-- WETTE 9.1.5 PREDECESSOR-INDUCTION SYNTACTIC SCAFFOLD
--
-- Premises 8,9,16,17 are support/infrastructure for the substantive premise
-- 18.  Each support formula below must be the conclusion of an actual certified
-- historical rule application.  Premise 18 remains intentionally absent.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969CertifiedHistoricalConclusionProducerExact as Producer
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915GeneratedScaffoldExact as Generated
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record InductionScaffoldProducerChain
    (initial : Context)
    (later : Later.Rule915LaterParameters) : Set₁ where
  constructor inductionScaffoldProducerChain
  field
    produce08 : Producer.CertifiedHistoricalConclusionProducer initial (Later.premise08 later)
    produce09 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce08) (Later.premise09 later)
    produce16 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce09) (Later.premise16 later)
    produce17 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce16) (Later.premise17 later)

open InductionScaffoldProducerChain public

inductionScaffoldTarget :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  InductionScaffoldProducerChain initial later → Context
inductionScaffoldTarget chain = Producer.producerTarget (produce17 chain)

inductionScaffoldTrace :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  (chain : InductionScaffoldProducerChain initial later) →
  PCRA.CertifiedRuleTrace historicalSystem initial
inductionScaffoldTrace chain =
  PCRA.appendCertifiedTrace (Producer.producerTrace (produce08 chain))
    (PCRA.appendCertifiedTrace (Producer.producerTrace (produce09 chain))
      (PCRA.appendCertifiedTrace (Producer.producerTrace (produce16 chain))
        (Producer.producerTrace (produce17 chain))))

p08AtTarget :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  (chain : InductionScaffoldProducerChain initial later) →
  Later.premise08 later Finite.∈Context inductionScaffoldTarget chain
p08AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce17 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce16 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce09 chain)) _
        (Producer.producedAtTarget (produce08 chain))))

p09AtTarget :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  (chain : InductionScaffoldProducerChain initial later) →
  Later.premise09 later Finite.∈Context inductionScaffoldTarget chain
p09AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce17 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce16 chain)) _
      (Producer.producedAtTarget (produce09 chain)))

p16AtTarget :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  (chain : InductionScaffoldProducerChain initial later) →
  Later.premise16 later Finite.∈Context inductionScaffoldTarget chain
p16AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce17 chain)) _
    (Producer.producedAtTarget (produce16 chain))

p17AtTarget :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  (chain : InductionScaffoldProducerChain initial later) →
  Later.premise17 later Finite.∈Context inductionScaffoldTarget chain
p17AtTarget chain = Producer.producedAtTarget (produce17 chain)

inductionScaffoldEvidenceAtTarget :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  (chain : InductionScaffoldProducerChain initial later) →
  Generated.InductionScaffoldEvidence (inductionScaffoldTarget chain) later
inductionScaffoldEvidenceAtTarget chain =
  Generated.inductionScaffoldEvidence
    (p08AtTarget chain) (p09AtTarget chain)
    (p16AtTarget chain) (p17AtTarget chain)

record Wette1969Rule915InductionScaffoldProducerBoundary : Set where
  constructor wette1969Rule915InductionScaffoldProducerBoundary
  field
    premise9IsAnExplicitHistoricalConclusionProducer : Bool
    premise9IsAnExplicitHistoricalConclusionProducerIsTrue :
      premise9IsAnExplicitHistoricalConclusionProducer ≡ true
    premises8_9_16_17GeneratedBeforePremise18 : Bool
    premises8_9_16_17GeneratedBeforePremise18IsTrue :
      premises8_9_16_17GeneratedBeforePremise18 ≡ true
    producerChainDoesNotManufacturePremise18 : Bool
    producerChainDoesNotManufacturePremise18IsTrue :
      producerChainDoesNotManufacturePremise18 ≡ true

canonicalWette1969Rule915InductionScaffoldProducerBoundary :
  Wette1969Rule915InductionScaffoldProducerBoundary
canonicalWette1969Rule915InductionScaffoldProducerBoundary =
  wette1969Rule915InductionScaffoldProducerBoundary true refl true refl true refl
