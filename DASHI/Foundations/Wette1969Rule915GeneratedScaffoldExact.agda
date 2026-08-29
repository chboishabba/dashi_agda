module DASHI.Foundations.Wette1969Rule915GeneratedScaffoldExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: GENERATED SYNTACTIC SCAFFOLD
--
-- Source-exact factorization from §1.632:
--   formation 1--7
--   syntactic scaffold 8--17 and 19--26
--   substantive L sockets 18 and 27.
--
-- The scaffold fields below are not bare memberships at the initial state.
-- Each stage is produced by a proof-carrying historical trace at the actual
-- state reached by the previous stage.  The final theorem transports all
-- generated evidence to one target and leaves *exactly* 18 and 27 as the two
-- major proof inputs required to certify 9.1.5.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact as Obligations
import DASHI.Foundations.Wette1969Rule915TwoProofCutsetExact as Cutset
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Later.WordTerm
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record InductionScaffoldEvidence
    (context : Context)
    (later : Later.Rule915LaterParameters) : Set where
  constructor inductionScaffoldEvidence
  field
    p08 : Later.premise08 later Finite.∈Context context
    p09 : Later.premise09 later Finite.∈Context context
    p16 : Later.premise16 later Finite.∈Context context
    p17 : Later.premise17 later Finite.∈Context context
open InductionScaffoldEvidence public

record IndependenceScaffoldEvidence
    (context : Context)
    (later : Later.Rule915LaterParameters) : Set where
  constructor independenceScaffoldEvidence
  field
    p19 : Later.premise19 later Finite.∈Context context
    p20 : Later.premise20 later Finite.∈Context context
    p21 : Later.premise21 later Finite.∈Context context
    p22 : Later.premise22 later Finite.∈Context context
    p23 : Later.premise23 later Finite.∈Context context
    p24 : Later.premise24 later Finite.∈Context context
    p25 : Later.premise25 later Finite.∈Context context
    p26 : Later.premise26 later Finite.∈Context context
open IndependenceScaffoldEvidence public

record Rule915GeneratedScaffoldChain
    (initial : Context)
    (firstSeven : Rule915.Rule915FirstSevenParameters)
    (later : Later.Rule915LaterParameters) : Set₁ where
  constructor rule915GeneratedScaffoldChain
  field
    formationTrace : PCRA.CertifiedRuleTrace historicalSystem initial
    formationProduced :
      Obligations.FirstSevenEvidence
        (PCRA.runCertifiedTrace historicalSystem formationTrace)
        (Later.completeTypedTranscription firstSeven later)

    sharedTrace :
      PCRA.CertifiedRuleTrace historicalSystem
        (PCRA.runCertifiedTrace historicalSystem formationTrace)
    sharedProduced :
      Obligations.Shared1015Evidence
        (PCRA.runCertifiedTrace historicalSystem sharedTrace)
        (Later.completeTypedTranscription firstSeven later)

    inductionScaffoldTrace :
      PCRA.CertifiedRuleTrace historicalSystem
        (PCRA.runCertifiedTrace historicalSystem sharedTrace)
    inductionScaffoldProduced :
      InductionScaffoldEvidence
        (PCRA.runCertifiedTrace historicalSystem inductionScaffoldTrace)
        later

    independenceScaffoldTrace :
      PCRA.CertifiedRuleTrace historicalSystem
        (PCRA.runCertifiedTrace historicalSystem inductionScaffoldTrace)
    independenceScaffoldProduced :
      IndependenceScaffoldEvidence
        (PCRA.runCertifiedTrace historicalSystem independenceScaffoldTrace)
        later

open Rule915GeneratedScaffoldChain public

generatedScaffoldTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  Rule915GeneratedScaffoldChain initial firstSeven later → Context
generatedScaffoldTarget chain =
  PCRA.runCertifiedTrace historicalSystem (independenceScaffoldTrace chain)

transportInductionScaffold :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  (trace : PCRA.CertifiedRuleTrace historicalSystem context) →
  InductionScaffoldEvidence context later →
  InductionScaffoldEvidence
    (PCRA.runCertifiedTrace historicalSystem trace) later
transportInductionScaffold trace evidence =
  inductionScaffoldEvidence
    (Closure.certifiedTracePreservesPriorFormula trace _ (p08 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (p09 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (p16 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (p17 evidence))

transportIndependenceScaffold :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  (trace : PCRA.CertifiedRuleTrace historicalSystem context) →
  IndependenceScaffoldEvidence context later →
  IndependenceScaffoldEvidence
    (PCRA.runCertifiedTrace historicalSystem trace) later
transportIndependenceScaffold trace evidence =
  independenceScaffoldEvidence
    (Closure.certifiedTracePreservesPriorFormula trace _ (p19 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (p20 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (p21 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (p22 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (p23 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (p24 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (p25 evidence))
    (Closure.certifiedTracePreservesPriorFormula trace _ (p26 evidence))

formationAtTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Rule915GeneratedScaffoldChain initial firstSeven later) →
  Obligations.FirstSevenEvidence
    (generatedScaffoldTarget chain)
    (Later.completeTypedTranscription firstSeven later)
formationAtTarget chain =
  Obligations.firstSevenEvidence
    (preserve _ (Obligations.e01 (formationProduced chain)))
    (preserve _ (Obligations.e02 (formationProduced chain)))
    (preserve _ (Obligations.e03 (formationProduced chain)))
    (preserve _ (Obligations.e04 (formationProduced chain)))
    (preserve _ (Obligations.e05 (formationProduced chain)))
    (preserve _ (Obligations.e06 (formationProduced chain)))
    (preserve _ (Obligations.e07 (formationProduced chain)))
  where
    preserve : ∀ formula →
      formula Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem (formationTrace chain)) →
      formula Finite.∈Context (generatedScaffoldTarget chain)
    preserve formula evidence =
      Closure.certifiedTracePreservesPriorFormula
        (independenceScaffoldTrace chain) formula
        (Closure.certifiedTracePreservesPriorFormula
          (inductionScaffoldTrace chain) formula
          (Closure.certifiedTracePreservesPriorFormula
            (sharedTrace chain) formula evidence))

sharedAtTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Rule915GeneratedScaffoldChain initial firstSeven later) →
  Obligations.Shared1015Evidence
    (generatedScaffoldTarget chain)
    (Later.completeTypedTranscription firstSeven later)
sharedAtTarget chain =
  Obligations.shared1015Evidence
    (preserve _ (Obligations.e10 (sharedProduced chain)))
    (preserve _ (Obligations.e11 (sharedProduced chain)))
    (preserve _ (Obligations.e12 (sharedProduced chain)))
    (preserve _ (Obligations.e13 (sharedProduced chain)))
    (preserve _ (Obligations.e14 (sharedProduced chain)))
    (preserve _ (Obligations.e15 (sharedProduced chain)))
  where
    preserve : ∀ formula →
      formula Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem (sharedTrace chain)) →
      formula Finite.∈Context (generatedScaffoldTarget chain)
    preserve formula evidence =
      Closure.certifiedTracePreservesPriorFormula
        (independenceScaffoldTrace chain) formula
        (Closure.certifiedTracePreservesPriorFormula
          (inductionScaffoldTrace chain) formula evidence)

inductionScaffoldAtTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Rule915GeneratedScaffoldChain initial firstSeven later) →
  InductionScaffoldEvidence (generatedScaffoldTarget chain) later
inductionScaffoldAtTarget chain =
  transportInductionScaffold
    (independenceScaffoldTrace chain)
    (inductionScaffoldProduced chain)

scaffoldEvidenceAtTarget :
  {initial : Context} →
  {firstSeven : Rule915.Rule915FirstSevenParameters} →
  {later : Later.Rule915LaterParameters} →
  (chain : Rule915GeneratedScaffoldChain initial firstSeven later) →
  Cutset.Rule915SyntacticScaffoldEvidence
    (generatedScaffoldTarget chain) firstSeven later
scaffoldEvidenceAtTarget chain =
  Cutset.rule915SyntacticScaffoldEvidence
    (Obligations.e01 formation) (Obligations.e02 formation)
    (Obligations.e03 formation) (Obligations.e04 formation)
    (Obligations.e05 formation) (Obligations.e06 formation)
    (Obligations.e07 formation)
    (p08 induction) (p09 induction)
    (Obligations.e10 shared) (Obligations.e11 shared)
    (Obligations.e12 shared) (Obligations.e13 shared)
    (Obligations.e14 shared) (Obligations.e15 shared)
    (p16 induction) (p17 induction)
    (p19 independence) (p20 independence) (p21 independence)
    (p22 independence) (p23 independence) (p24 independence)
    (p25 independence) (p26 independence)
  where
    formation = formationAtTarget chain
    shared = sharedAtTarget chain
    induction = inductionScaffoldAtTarget chain
    independence = independenceScaffoldProduced chain

selectRule915FromGeneratedScaffoldAndTwoProofs :
  {initial : Context} →
  (firstSeven : Rule915.Rule915FirstSevenParameters) →
  (later : Later.Rule915LaterParameters) →
  (recursivePredicate : WordTerm) →
  (chain : Rule915GeneratedScaffoldChain initial firstSeven later) →
  Cutset.Rule915MajorProofEvidence (generatedScaffoldTarget chain) later →
  PCRA.SelectedRuleApplication historicalSystem (generatedScaffoldTarget chain)
selectRule915FromGeneratedScaffoldAndTwoProofs
  firstSeven later recursivePredicate chain major =
  Cutset.selectRule915FromTwoProofCutset
    firstSeven later recursivePredicate (scaffoldEvidenceAtTarget chain) major

record Wette1969Rule915GeneratedScaffoldBoundary : Set where
  constructor wette1969Rule915GeneratedScaffoldBoundary
  field
    formationAndEighteenScaffoldSlotsAreProducedByHistoricalTraces : Bool
    formationAndEighteenScaffoldSlotsAreProducedByHistoricalTracesIsTrue :
      formationAndEighteenScaffoldSlotsAreProducedByHistoricalTraces ≡ true
    shared1015IsProducedOnceAndReused : Bool
    shared1015IsProducedOnceAndReusedIsTrue : shared1015IsProducedOnceAndReused ≡ true
    premise9IsIncludedInInductionScaffold : Bool
    premise9IsIncludedInInductionScaffoldIsTrue : premise9IsIncludedInInductionScaffold ≡ true
    onlyPremises18And27RemainAsMajorProofSockets : Bool
    onlyPremises18And27RemainAsMajorProofSocketsIsTrue :
      onlyPremises18And27RemainAsMajorProofSockets ≡ true
    generatedScaffoldMeansFreshnessForArbitraryWords : Bool
    generatedScaffoldMeansFreshnessForArbitraryWordsIsFalse :
      generatedScaffoldMeansFreshnessForArbitraryWords ≡ false
    twoMajorProofSocketsAreUniversallyDischarged : Bool
    twoMajorProofSocketsAreUniversallyDischargedIsFalse :
      twoMajorProofSocketsAreUniversallyDischarged ≡ false

canonicalWette1969Rule915GeneratedScaffoldBoundary :
  Wette1969Rule915GeneratedScaffoldBoundary
canonicalWette1969Rule915GeneratedScaffoldBoundary =
  wette1969Rule915GeneratedScaffoldBoundary
    true refl true refl true refl true refl false refl false refl
