module DASHI.Foundations.Wette1969IndependenceBranch2425ProducerExact where

------------------------------------------------------------------------
-- WETTE 9.1.5 DEFINIENS-INDEPENDENCE BRANCH: INTERNAL 24/25 PRODUCTION
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact as Obligations
import DASHI.Foundations.Wette1969DependentTwoStageSubstitutionExact as TwoStage
import DASHI.Foundations.Wette1969CertifiedTwoStageIIDerivationExact as CertifiedTwoStage
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record Premise2425ProducerChain
    (initial : Context)
    (later : Later.Rule915LaterParameters) : Set₁ where
  constructor premise2425ProducerChain
  field
    stages24 : TwoStage.DependentTwoStageSubstitution
    stages24Matches : TwoStage.pairedII stages24 ≡ Later.premise24 later
    derivation24 :
      CertifiedTwoStage.CertifiedTwoStageIIDerivation initial stages24

    stages25 : TwoStage.DependentTwoStageSubstitution
    stages25Matches : TwoStage.pairedII stages25 ≡ Later.premise25 later
    derivation25 :
      CertifiedTwoStage.CertifiedTwoStageIIDerivation
        (PCRA.runCertifiedTrace historicalSystem
          (CertifiedTwoStage.pairedTrace derivation24))
        stages25

open Premise2425ProducerChain public

contextAfter24 :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  Premise2425ProducerChain initial later → Context
contextAfter24 chain =
  PCRA.runCertifiedTrace historicalSystem
    (CertifiedTwoStage.pairedTrace (derivation24 chain))

finalContext :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  Premise2425ProducerChain initial later → Context
finalContext chain =
  PCRA.runCertifiedTrace historicalSystem
    (CertifiedTwoStage.pairedTrace (derivation25 chain))

premise24AtFirstTarget :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  (chain : Premise2425ProducerChain initial later) →
  Later.premise24 later Finite.∈Context contextAfter24 chain
premise24AtFirstTarget {later = later} chain
  rewrite sym (stages24Matches chain) =
  CertifiedTwoStage.pairedIIAvailable (derivation24 chain)

premise24AtFinal :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  (chain : Premise2425ProducerChain initial later) →
  Later.premise24 later Finite.∈Context finalContext chain
premise24AtFinal {later = later} chain =
  Closure.certifiedTracePreservesPriorFormula
    (CertifiedTwoStage.pairedTrace (derivation25 chain))
    (Later.premise24 later)
    (premise24AtFirstTarget chain)

premise25AtFinal :
  {initial : Context} → {later : Later.Rule915LaterParameters} →
  (chain : Premise2425ProducerChain initial later) →
  Later.premise25 later Finite.∈Context finalContext chain
premise25AtFinal {later = later} chain
  rewrite sym (stages25Matches chain) =
  CertifiedTwoStage.pairedIIAvailable (derivation25 chain)

record IndependenceNon2425Evidence
    (context : Context)
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters) : Set where
  constructor independenceNon2425Evidence
  field
    shared :
      Obligations.Shared1015Evidence
        context
        (Later.completeTypedTranscription firstSeven later)
    e19 : Later.premise19 later Finite.∈Context context
    e20 : Later.premise20 later Finite.∈Context context
    e21 : Later.premise21 later Finite.∈Context context
    e22 : Later.premise22 later Finite.∈Context context
    e23 : Later.premise23 later Finite.∈Context context
    e26 : Later.premise26 later Finite.∈Context context
    e27 : Later.premise27 later Finite.∈Context context

open IndependenceNon2425Evidence public

transportNon2425 :
  {context : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (trace : PCRA.CertifiedRuleTrace historicalSystem context) →
  IndependenceNon2425Evidence context firstSeven later →
  IndependenceNon2425Evidence
    (PCRA.runCertifiedTrace historicalSystem trace) firstSeven later
transportNon2425 trace evidence =
  independenceNon2425Evidence
    (Obligations.shared1015Evidence
      (Closure.certifiedTracePreservesPriorFormula trace _
        (Obligations.e10 (shared evidence)))
      (Closure.certifiedTracePreservesPriorFormula trace _
        (Obligations.e11 (shared evidence)))
      (Closure.certifiedTracePreservesPriorFormula trace _
        (Obligations.e12 (shared evidence)))
      (Closure.certifiedTracePreservesPriorFormula trace _
        (Obligations.e13 (shared evidence)))
      (Closure.certifiedTracePreservesPriorFormula trace _
        (Obligations.e14 (shared evidence)))
      (Closure.certifiedTracePreservesPriorFormula trace _
        (Obligations.e15 (shared evidence))))
    (Closure.certifiedTracePreservesPriorFormula trace _ (e19 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (e20 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (e21 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (e22 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (e23 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (e26 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (e27 evidence))

finalNon2425Evidence :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  IndependenceNon2425Evidence initial firstSeven later →
  (chain : Premise2425ProducerChain initial later) →
  IndependenceNon2425Evidence (finalContext chain) firstSeven later
finalNon2425Evidence evidence chain =
  transportNon2425
    (CertifiedTwoStage.pairedTrace (derivation25 chain))
    (transportNon2425
      (CertifiedTwoStage.pairedTrace (derivation24 chain))
      evidence)

independenceBranchAfter2425 :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (evidence : IndependenceNon2425Evidence initial firstSeven later) →
  (chain : Premise2425ProducerChain initial later) →
  Obligations.DefiniensIndependenceBranch
    (finalContext chain)
    (Later.completeTypedTranscription firstSeven later)
    (shared (finalNon2425Evidence evidence chain))
independenceBranchAfter2425 firstSeven later evidence chain =
  Obligations.definiensIndependenceBranch
    (e19 finalEvidence)
    (e20 finalEvidence)
    (e21 finalEvidence)
    (e22 finalEvidence)
    (e23 finalEvidence)
    (premise24AtFinal chain)
    (premise25AtFinal chain)
    (e26 finalEvidence)
    (e27 finalEvidence)
  where
    finalEvidence = finalNon2425Evidence evidence chain

record Wette1969IndependenceBranch2425ProducerBoundary : Set where
  constructor wette1969IndependenceBranch2425ProducerBoundary
  field
    independencePremises24And25NoLongerExternalEvidence : Bool
    independencePremises24And25NoLongerExternalEvidenceIsTrue :
      independencePremises24And25NoLongerExternalEvidence ≡ true
    generated24PersistsAcross25ProducerTrace : Bool
    generated24PersistsAcross25ProducerTraceIsTrue :
      generated24PersistsAcross25ProducerTrace ≡ true
    remainingIndependenceEvidenceNowConcentratedIn19To23And26To27 : Bool
    remainingIndependenceEvidenceNowConcentratedIn19To23And26To27IsTrue :
      remainingIndependenceEvidenceNowConcentratedIn19To23And26To27 ≡ true
    generated2425AreAlreadySemanticIndependenceProof : Bool
    generated2425AreAlreadySemanticIndependenceProofIsFalse :
      generated2425AreAlreadySemanticIndependenceProof ≡ false

canonicalWette1969IndependenceBranch2425ProducerBoundary :
  Wette1969IndependenceBranch2425ProducerBoundary
canonicalWette1969IndependenceBranch2425ProducerBoundary =
  wette1969IndependenceBranch2425ProducerBoundary
    true refl true refl true refl false refl
