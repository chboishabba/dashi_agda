module DASHI.Foundations.Wette1969Rule915Shared1015ProducerExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969CertifiedHistoricalConclusionProducerExact as Producer
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact as Obligations
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record Shared1015ProducerChain
    (initial : Context)
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters) : Set₁ where
  constructor shared1015ProducerChain
  field
    produce10 : Producer.CertifiedHistoricalConclusionProducer initial (Later.premise10 later)
    produce11 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce10) (Later.premise11 later)
    produce12 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce11) (Later.premise12 later)
    produce13 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce12) (Later.premise13 later)
    produce14 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce13) (Later.premise14 later)
    produce15 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce14) (Later.premise15 later)

open Shared1015ProducerChain public

sharedTarget :
  {initial : Context} → {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  Shared1015ProducerChain initial firstSeven later → Context
sharedTarget chain = Producer.producerTarget (produce15 chain)

sharedTrace :
  {initial : Context} → {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Shared1015ProducerChain initial firstSeven later) →
  PCRA.CertifiedRuleTrace historicalSystem initial
sharedTrace chain =
  PCRA.appendCertifiedTrace (Producer.producerTrace (produce10 chain))
    (PCRA.appendCertifiedTrace (Producer.producerTrace (produce11 chain))
      (PCRA.appendCertifiedTrace (Producer.producerTrace (produce12 chain))
        (PCRA.appendCertifiedTrace (Producer.producerTrace (produce13 chain))
          (PCRA.appendCertifiedTrace (Producer.producerTrace (produce14 chain))
            (Producer.producerTrace (produce15 chain))))))

p10AtTarget :
  {initial : Context} → {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Shared1015ProducerChain initial firstSeven later) →
  Later.premise10 later Finite.∈Context sharedTarget chain
p10AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce15 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce14 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce13 chain)) _
        (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce12 chain)) _
          (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce11 chain)) _
            (Producer.producedAtTarget (produce10 chain))))))

p11AtTarget :
  {initial : Context} → {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Shared1015ProducerChain initial firstSeven later) →
  Later.premise11 later Finite.∈Context sharedTarget chain
p11AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce15 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce14 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce13 chain)) _
        (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce12 chain)) _
          (Producer.producedAtTarget (produce11 chain)))))

p12AtTarget :
  {initial : Context} → {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Shared1015ProducerChain initial firstSeven later) →
  Later.premise12 later Finite.∈Context sharedTarget chain
p12AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce15 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce14 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce13 chain)) _
        (Producer.producedAtTarget (produce12 chain))))

p13AtTarget :
  {initial : Context} → {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Shared1015ProducerChain initial firstSeven later) →
  Later.premise13 later Finite.∈Context sharedTarget chain
p13AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce15 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce14 chain)) _
      (Producer.producedAtTarget (produce13 chain)))

p14AtTarget :
  {initial : Context} → {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Shared1015ProducerChain initial firstSeven later) →
  Later.premise14 later Finite.∈Context sharedTarget chain
p14AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce15 chain)) _
    (Producer.producedAtTarget (produce14 chain))

p15AtTarget :
  {initial : Context} → {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Shared1015ProducerChain initial firstSeven later) →
  Later.premise15 later Finite.∈Context sharedTarget chain
p15AtTarget chain = Producer.producedAtTarget (produce15 chain)

sharedEvidenceAtTarget :
  {initial : Context} → {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Shared1015ProducerChain initial firstSeven later) →
  Obligations.Shared1015Evidence
    (sharedTarget chain)
    (Later.completeTypedTranscription firstSeven later)
sharedEvidenceAtTarget chain =
  Obligations.shared1015Evidence
    (p10AtTarget chain) (p11AtTarget chain) (p12AtTarget chain)
    (p13AtTarget chain) (p14AtTarget chain) (p15AtTarget chain)

record Wette1969Rule915Shared1015ProducerBoundary : Set where
  constructor wette1969Rule915Shared1015ProducerBoundary
  field
    eachSharedSlotMustBeActualHistoricalRuleConclusion : Bool
    eachSharedSlotMustBeActualHistoricalRuleConclusionIsTrue :
      eachSharedSlotMustBeActualHistoricalRuleConclusion ≡ true
    shared1015ProducedExactlyOnceBeforeBranching : Bool
    shared1015ProducedExactlyOnceBeforeBranchingIsTrue :
      shared1015ProducedExactlyOnceBeforeBranching ≡ true
    sharedProductionDoesNotProvePremise18Or27 : Bool
    sharedProductionDoesNotProvePremise18Or27IsTrue :
      sharedProductionDoesNotProvePremise18Or27 ≡ true

canonicalWette1969Rule915Shared1015ProducerBoundary :
  Wette1969Rule915Shared1015ProducerBoundary
canonicalWette1969Rule915Shared1015ProducerBoundary =
  wette1969Rule915Shared1015ProducerBoundary true refl true refl true refl
