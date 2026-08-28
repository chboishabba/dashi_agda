module DASHI.Foundations.Wette1969IndependenceBranchGeneratedCoreExact where

------------------------------------------------------------------------
-- WETTE 9.1.5 DEFINIENS-INDEPENDENCE BRANCH: GENERATED 19--21 AND 24--25
--
-- The external residue of the branch is now narrowed to:
--   shared premises 10--15,
--   premise 22 (compound mark/context freshness),
--   premise 23 (tuple/definiens freshness),
--   premise 26 (abbreviation),
--   premise 27 (decisive L-independence judgement).
--
-- Premises 19/20 are produced by rule 4, premise 21 by 8.1.17, and 24/25 by
-- certified 8.2 derivations plus 8.2.8.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact as Obligations
import DASHI.Foundations.Wette1969Rule915Premise1921DerivationExact as Produce1921
import DASHI.Foundations.Wette1969IndependenceBranch2425ProducerExact as Produce2425
import DASHI.Foundations.Wette1969CertifiedTwoStageIIDerivationExact as CertifiedTwoStage
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record IndependenceResidualEvidence
    (context : Context)
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters) : Set where
  constructor independenceResidualEvidence
  field
    shared :
      Obligations.Shared1015Evidence
        context
        (Later.completeTypedTranscription firstSeven later)
    e22 : Later.premise22 later Finite.∈Context context
    e23 : Later.premise23 later Finite.∈Context context
    e26 : Later.premise26 later Finite.∈Context context
    e27 : Later.premise27 later Finite.∈Context context

open IndependenceResidualEvidence public

transportResidual :
  {context : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (trace : PCRA.CertifiedRuleTrace historicalSystem context) →
  IndependenceResidualEvidence context firstSeven later →
  IndependenceResidualEvidence
    (PCRA.runCertifiedTrace historicalSystem trace) firstSeven later
transportResidual trace evidence =
  independenceResidualEvidence
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
    (Closure.certifiedTracePreservesPriorFormula trace _ (e22 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (e23 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (e26 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (e27 evidence))

record IndependenceGeneratedCore
    (initial : Context)
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters) : Set₁ where
  constructor independenceGeneratedCore
  field
    residualAtInitial : IndependenceResidualEvidence initial firstSeven later
    marks1921 : Produce1921.Premise1921Inputs initial later
    substitutions2425 :
      Produce2425.Premise2425ProducerChain
        (Produce1921.premise1921Target marks1921)
        later

open IndependenceGeneratedCore public

finalContext :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  IndependenceGeneratedCore initial firstSeven later → Context
finalContext core = Produce2425.finalContext (substitutions2425 core)

residualAtFinal :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (core : IndependenceGeneratedCore initial firstSeven later) →
  IndependenceResidualEvidence (finalContext core) firstSeven later
residualAtFinal core =
  transportResidual
    (CertifiedTwoStage.pairedTrace
      (Produce2425.derivation25 (substitutions2425 core)))
    (transportResidual
      (CertifiedTwoStage.pairedTrace
        (Produce2425.derivation24 (substitutions2425 core)))
      (transportResidual
        (Produce1921.premise1921Trace (marks1921 core))
        (residualAtInitial core)))

premise19AtFinal :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (core : IndependenceGeneratedCore initial firstSeven later) →
  Later.premise19 later Finite.∈Context finalContext core
premise19AtFinal core =
  Closure.certifiedTracePreservesPriorFormula
    (CertifiedTwoStage.pairedTrace
      (Produce2425.derivation25 (substitutions2425 core))) _
    (Closure.certifiedTracePreservesPriorFormula
      (CertifiedTwoStage.pairedTrace
        (Produce2425.derivation24 (substitutions2425 core))) _
      (Produce1921.premise19Available (marks1921 core)))

premise20AtFinal :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (core : IndependenceGeneratedCore initial firstSeven later) →
  Later.premise20 later Finite.∈Context finalContext core
premise20AtFinal core =
  Closure.certifiedTracePreservesPriorFormula
    (CertifiedTwoStage.pairedTrace
      (Produce2425.derivation25 (substitutions2425 core))) _
    (Closure.certifiedTracePreservesPriorFormula
      (CertifiedTwoStage.pairedTrace
        (Produce2425.derivation24 (substitutions2425 core))) _
      (Produce1921.premise20Available (marks1921 core)))

premise21AtFinal :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (core : IndependenceGeneratedCore initial firstSeven later) →
  Later.premise21 later Finite.∈Context finalContext core
premise21AtFinal core =
  Closure.certifiedTracePreservesPriorFormula
    (CertifiedTwoStage.pairedTrace
      (Produce2425.derivation25 (substitutions2425 core))) _
    (Closure.certifiedTracePreservesPriorFormula
      (CertifiedTwoStage.pairedTrace
        (Produce2425.derivation24 (substitutions2425 core))) _
      (Produce1921.premise21Available (marks1921 core)))

independenceBranch :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (core : IndependenceGeneratedCore initial firstSeven later) →
  Obligations.DefiniensIndependenceBranch
    (finalContext core)
    (Later.completeTypedTranscription firstSeven later)
    (shared (residualAtFinal core))
independenceBranch firstSeven later core =
  Obligations.definiensIndependenceBranch
    (premise19AtFinal core)
    (premise20AtFinal core)
    (premise21AtFinal core)
    (e22 finalResidual)
    (e23 finalResidual)
    (Produce2425.premise24AtFinal (substitutions2425 core))
    (Produce2425.premise25AtFinal (substitutions2425 core))
    (e26 finalResidual)
    (e27 finalResidual)
  where
    finalResidual = residualAtFinal core

record Wette1969IndependenceBranchGeneratedCoreBoundary : Set where
  constructor wette1969IndependenceBranchGeneratedCoreBoundary
  field
    premises19Through21NowHistoricalProducerOutputs : Bool
    premises19Through21NowHistoricalProducerOutputsIsTrue :
      premises19Through21NowHistoricalProducerOutputs ≡ true
    premises24And25NowHistoricalProducerOutputs : Bool
    premises24And25NowHistoricalProducerOutputsIsTrue :
      premises24And25NowHistoricalProducerOutputs ≡ true
    independenceExternalResidueReducedTo22_23_26_27PlusSharedCore : Bool
    independenceExternalResidueReducedTo22_23_26_27PlusSharedCoreIsTrue :
      independenceExternalResidueReducedTo22_23_26_27PlusSharedCore ≡ true
    generatedBranchCoreAlreadyProvesPremise27 : Bool
    generatedBranchCoreAlreadyProvesPremise27IsFalse :
      generatedBranchCoreAlreadyProvesPremise27 ≡ false

canonicalWette1969IndependenceBranchGeneratedCoreBoundary :
  Wette1969IndependenceBranchGeneratedCoreBoundary
canonicalWette1969IndependenceBranchGeneratedCoreBoundary =
  wette1969IndependenceBranchGeneratedCoreBoundary
    true refl true refl true refl false refl
