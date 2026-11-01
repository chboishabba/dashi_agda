module DASHI.Foundations.Wette1969Rule915FormationProducerExact where

------------------------------------------------------------------------
-- WETTE 9.1.5 FIRST-SEVEN FORMATION PRODUCERS
--
-- The first seven premises are not part of the §1.632 twenty-premise L block,
-- but a claim that *all* non-major admissibility is generated must not confuse
-- literal transcription with derivation.  This module therefore requires every
-- first-seven formula to occur as the conclusion of an actual certified
-- historical rule application before the later scaffold begins.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969CertifiedHistoricalConclusionProducerExact as Producer
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact as Obligations
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record FormationProducerChain
    (initial : Context)
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters) : Set₁ where
  constructor formationProducerChain
  field
    produce01 : Producer.CertifiedHistoricalConclusionProducer initial (Rule915.premise915-01 firstSeven)
    produce02 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce01) (Rule915.premise915-02 firstSeven)
    produce03 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce02) (Rule915.premise915-03 firstSeven)
    produce04 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce03) (Rule915.premise915-04 firstSeven)
    produce05 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce04) (Rule915.premise915-05 firstSeven)
    produce06 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce05) (Rule915.premise915-06 firstSeven)
    produce07 : Producer.CertifiedHistoricalConclusionProducer (Producer.producerTarget produce06) (Rule915.premise915-07 firstSeven)

open FormationProducerChain public

formationTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  FormationProducerChain initial firstSeven later → Context
formationTarget chain = Producer.producerTarget (produce07 chain)

formationTrace :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : FormationProducerChain initial firstSeven later) →
  PCRA.CertifiedRuleTrace historicalSystem initial
formationTrace chain =
  PCRA.appendCertifiedTrace (Producer.producerTrace (produce01 chain))
    (PCRA.appendCertifiedTrace (Producer.producerTrace (produce02 chain))
      (PCRA.appendCertifiedTrace (Producer.producerTrace (produce03 chain))
        (PCRA.appendCertifiedTrace (Producer.producerTrace (produce04 chain))
          (PCRA.appendCertifiedTrace (Producer.producerTrace (produce05 chain))
            (PCRA.appendCertifiedTrace (Producer.producerTrace (produce06 chain))
              (Producer.producerTrace (produce07 chain)))))))

p01AtTarget : {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  (chain : FormationProducerChain initial firstSeven later) →
  Rule915.premise915-01 firstSeven Finite.∈Context formationTarget chain
p01AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce07 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce06 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce05 chain)) _
        (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce04 chain)) _
          (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce03 chain)) _
            (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce02 chain)) _
              (Producer.producedAtTarget (produce01 chain)))))))

p02AtTarget : {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  (chain : FormationProducerChain initial firstSeven later) →
  Rule915.premise915-02 firstSeven Finite.∈Context formationTarget chain
p02AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce07 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce06 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce05 chain)) _
        (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce04 chain)) _
          (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce03 chain)) _
            (Producer.producedAtTarget (produce02 chain))))))

p03AtTarget : {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  (chain : FormationProducerChain initial firstSeven later) →
  Rule915.premise915-03 firstSeven Finite.∈Context formationTarget chain
p03AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce07 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce06 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce05 chain)) _
        (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce04 chain)) _
          (Producer.producedAtTarget (produce03 chain)))))

p04AtTarget : {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  (chain : FormationProducerChain initial firstSeven later) →
  Rule915.premise915-04 firstSeven Finite.∈Context formationTarget chain
p04AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce07 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce06 chain)) _
      (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce05 chain)) _
        (Producer.producedAtTarget (produce04 chain))))

p05AtTarget : {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  (chain : FormationProducerChain initial firstSeven later) →
  Rule915.premise915-05 firstSeven Finite.∈Context formationTarget chain
p05AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce07 chain)) _
    (Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce06 chain)) _
      (Producer.producedAtTarget (produce05 chain)))

p06AtTarget : {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  (chain : FormationProducerChain initial firstSeven later) →
  Rule915.premise915-06 firstSeven Finite.∈Context formationTarget chain
p06AtTarget chain =
  Closure.certifiedTracePreservesPriorFormula (Producer.producerTrace (produce07 chain)) _
    (Producer.producedAtTarget (produce06 chain))

p07AtTarget : {initial : Context} {firstSeven : Rule915.Rule915FirstSevenParameters}
  {later : Later.Rule915LaterParameters} →
  (chain : FormationProducerChain initial firstSeven later) →
  Rule915.premise915-07 firstSeven Finite.∈Context formationTarget chain
p07AtTarget chain = Producer.producedAtTarget (produce07 chain)

formationEvidenceAtTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : FormationProducerChain initial firstSeven later) →
  Obligations.FirstSevenEvidence
    (formationTarget chain)
    (Later.completeTypedTranscription firstSeven later)
formationEvidenceAtTarget chain =
  Obligations.firstSevenEvidence
    (p01AtTarget chain) (p02AtTarget chain) (p03AtTarget chain)
    (p04AtTarget chain) (p05AtTarget chain) (p06AtTarget chain)
    (p07AtTarget chain)

record Wette1969Rule915FormationProducerBoundary : Set where
  constructor wette1969Rule915FormationProducerBoundary
  field
    literalFirstSevenNowSeparatedFromTheirDerivability : Bool
    literalFirstSevenNowSeparatedFromTheirDerivabilityIsTrue :
      literalFirstSevenNowSeparatedFromTheirDerivability ≡ true
    everyFirstSevenPremiseMustBeHistoricalRuleConclusion : Bool
    everyFirstSevenPremiseMustBeHistoricalRuleConclusionIsTrue :
      everyFirstSevenPremiseMustBeHistoricalRuleConclusion ≡ true
    firstSevenFormationNoLongerSatisfiedByBareMembershipOnly : Bool
    firstSevenFormationNoLongerSatisfiedByBareMembershipOnlyIsTrue :
      firstSevenFormationNoLongerSatisfiedByBareMembershipOnly ≡ true

canonicalWette1969Rule915FormationProducerBoundary :
  Wette1969Rule915FormationProducerBoundary
canonicalWette1969Rule915FormationProducerBoundary =
  wette1969Rule915FormationProducerBoundary true refl true refl true refl
