module DASHI.Foundations.Wette1969Rule915IndependenceScaffoldProducerExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969CertifiedHistoricalConclusionProducerExact as Producer
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915GeneratedScaffoldExact as Generated
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record IndependenceScaffoldProducerChain
    (initial : Context)
    (later : Later.Rule915LaterParameters) : Set₁ where
  constructor independenceScaffoldProducerChain
  field
    produce19 : Producer.CertifiedHistoricalConclusionProducer initial (Later.premise19 later)
    produce20 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce19) (Later.premise20 later)
    produce21 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce20) (Later.premise21 later)
    produce22 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce21) (Later.premise22 later)
    produce23 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce22) (Later.premise23 later)
    produce24 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce23) (Later.premise24 later)
    produce25 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce24) (Later.premise25 later)
    produce26 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce25) (Later.premise26 later)

open IndependenceScaffoldProducerChain public

independenceScaffoldTarget :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  IndependenceScaffoldProducerChain initial later → Context
independenceScaffoldTarget chain = Producer.producerTarget (produce26 chain)

independenceScaffoldTrace :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  (chain : IndependenceScaffoldProducerChain initial later) →
  PCRA.CertifiedRuleTrace historicalSystem initial
independenceScaffoldTrace chain =
  PCRA.appendCertifiedTrace (Producer.producerTrace (produce19 chain))
    (PCRA.appendCertifiedTrace (Producer.producerTrace (produce20 chain))
      (PCRA.appendCertifiedTrace (Producer.producerTrace (produce21 chain))
        (PCRA.appendCertifiedTrace (Producer.producerTrace (produce22 chain))
          (PCRA.appendCertifiedTrace (Producer.producerTrace (produce23 chain))
            (PCRA.appendCertifiedTrace (Producer.producerTrace (produce24 chain))
              (PCRA.appendCertifiedTrace (Producer.producerTrace (produce25 chain))
                (Producer.producerTrace (produce26 chain))))))))

p19AtTarget : {initial : Context} {later : Later.Rule915LaterParameters} →
  (chain : IndependenceScaffoldProducerChain initial later) →
  Later.premise19 later Finite.∈Context independenceScaffoldTarget chain
p19AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce26 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce25 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce24 chain)) _
        (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce23 chain)) _
          (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce22 chain)) _
            (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce21 chain)) _
              (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce20 chain)) _
                (Producer.producedAtTarget (produce19 chain))))))))

p20AtTarget : {initial : Context} {later : Later.Rule915LaterParameters} →
  (chain : IndependenceScaffoldProducerChain initial later) →
  Later.premise20 later Finite.∈Context independenceScaffoldTarget chain
p20AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce26 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce25 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce24 chain)) _
        (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce23 chain)) _
          (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce22 chain)) _
            (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce21 chain)) _
              (Producer.producedAtTarget (produce20 chain)))))))

p21AtTarget : {initial : Context} {later : Later.Rule915LaterParameters} →
  (chain : IndependenceScaffoldProducerChain initial later) →
  Later.premise21 later Finite.∈Context independenceScaffoldTarget chain
p21AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce26 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce25 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce24 chain)) _
        (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce23 chain)) _
          (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce22 chain)) _
            (Producer.producedAtTarget (produce21 chain))))))

p22AtTarget : {initial : Context} {later : Later.Rule915LaterParameters} →
  (chain : IndependenceScaffoldProducerChain initial later) →
  Later.premise22 later Finite.∈Context independenceScaffoldTarget chain
p22AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce26 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce25 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce24 chain)) _
        (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce23 chain)) _
          (Producer.producedAtTarget (produce22 chain)))))

p23AtTarget : {initial : Context} {later : Later.Rule915LaterParameters} →
  (chain : IndependenceScaffoldProducerChain initial later) →
  Later.premise23 later Finite.∈Context independenceScaffoldTarget chain
p23AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce26 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce25 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce24 chain)) _
        (Producer.producedAtTarget (produce23 chain))))

p24AtTarget : {initial : Context} {later : Later.Rule915LaterParameters} →
  (chain : IndependenceScaffoldProducerChain initial later) →
  Later.premise24 later Finite.∈Context independenceScaffoldTarget chain
p24AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce26 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce25 chain)) _
      (Producer.producedAtTarget (produce24 chain)))

p25AtTarget : {initial : Context} {later : Later.Rule915LaterParameters} →
  (chain : IndependenceScaffoldProducerChain initial later) →
  Later.premise25 later Finite.∈Context independenceScaffoldTarget chain
p25AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce26 chain)) _
    (Producer.producedAtTarget (produce25 chain))

p26AtTarget : {initial : Context} {later : Later.Rule915LaterParameters} →
  (chain : IndependenceScaffoldProducerChain initial later) →
  Later.premise26 later Finite.∈Context independenceScaffoldTarget chain
p26AtTarget chain = Producer.producedAtTarget (produce26 chain)

independenceScaffoldEvidenceAtTarget :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  (chain : IndependenceScaffoldProducerChain initial later) →
  Generated.IndependenceScaffoldEvidence (independenceScaffoldTarget chain) later
independenceScaffoldEvidenceAtTarget chain =
  Generated.independenceScaffoldEvidence
    (p19AtTarget chain) (p20AtTarget chain) (p21AtTarget chain)
    (p22AtTarget chain) (p23AtTarget chain) (p24AtTarget chain)
    (p25AtTarget chain) (p26AtTarget chain)

record Wette1969Rule915IndependenceScaffoldProducerBoundary : Set where
  constructor wette1969Rule915IndependenceScaffoldProducerBoundary
  field
    premises19Through26MustBeHistoricalRuleConclusions : Bool
    premises19Through26MustBeHistoricalRuleConclusionsIsTrue :
      premises19Through26MustBeHistoricalRuleConclusions ≡ true
    premises22And23RemainRealFreshnessProducerObligations : Bool
    premises22And23RemainRealFreshnessProducerObligationsIsTrue :
      premises22And23RemainRealFreshnessProducerObligations ≡ true
    premise26MustComeFromHistoricalAbbreviationProduction : Bool
    premise26MustComeFromHistoricalAbbreviationProductionIsTrue :
      premise26MustComeFromHistoricalAbbreviationProduction ≡ true
    producerChainDoesNotManufacturePremise27 : Bool
    producerChainDoesNotManufacturePremise27IsTrue :
      producerChainDoesNotManufacturePremise27 ≡ true

canonicalWette1969Rule915IndependenceScaffoldProducerBoundary :
  Wette1969Rule915IndependenceScaffoldProducerBoundary
canonicalWette1969Rule915IndependenceScaffoldProducerBoundary =
  wette1969Rule915IndependenceScaffoldProducerBoundary
    true refl true refl true refl true refl
