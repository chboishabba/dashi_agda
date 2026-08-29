module DASHI.Foundations.Wette1969Rule915ZeroArityFalsumScaffoldExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969CertifiedHistoricalConclusionProducerExact as Producer
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915FormationProducerExact as Formation
import DASHI.Foundations.Wette1969Rule915Shared1015ProducerExact as Shared
import DASHI.Foundations.Wette1969Rule915InductionScaffoldProducerExact as Induction
import DASHI.Foundations.Wette1969Rule915IndependenceScaffoldProducerExact as Independence
import DASHI.Foundations.Wette1969Rule915SourceExactScaffoldCutsetExact as Source
import DASHI.Foundations.Wette1969Rule915ZeroArityFalsumInstanceExact as I
import DASHI.Foundations.Wette1969ZeroArityWitnessRulesExact as R
import DASHI.Foundations.Wette1969Rule34ObjectProducerExact as Rule34
import DASHI.Foundations.Wette1969Rule83TupleDerivationExact as Rule83
import DASHI.Foundations.Wette1969Rule7FusionDerivationExact as Rule7
import DASHI.Foundations.Wette1969Rule10AbbreviationDerivationExact as Rule10
import DASHI.Foundations.Wette1969Rule8112FreshnessDerivationExact as Rule8112
import DASHI.Foundations.Wette1969Rule8117PredicateMarkFreshnessExact as Rule8117
import DASHI.Foundations.Wette1969FreshnessSpineExact as Fresh
import DASHI.Foundations.Wette1969SubstitutionRuleSpineExact as Subst
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

------------------------------------------------------------------------
-- Small producer combinators.
------------------------------------------------------------------------

p01Producer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c
    (Rule915.premise915-01 I.canonicalFirstSeven)
p01Producer c = Producer.singleStepProducer (R.select0 c R.rule21 refl) refl

mark0Producer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c
    (Judgment.predicateMarkArity I.zeroWord I.mark0)
mark0Producer c =
  Producer.certifiedHistoricalConclusionProducer
    (PCRA.choose s0 PCRA.done) sm refl PCRA.done
  where
    s0 = R.select0 c R.rule01 refl
    c1 = PCRA.applySelected historicalSystem s0
    k0 : Judgment.naturalNumber I.zeroWord Finite.∈Context c1
    k0 = Closure.certifiedConclusionAvailable c s0
    sm = Rule34.selectRule4 c1 I.zeroWord I.zeroWord k0 k0

mark1Producer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c
    (Judgment.predicateMarkArity I.zeroWord I.mark1)
mark1Producer c =
  Producer.certifiedHistoricalConclusionProducer
    (PCRA.choose s0 (PCRA.choose s1 PCRA.done)) sm refl PCRA.done
  where
    s0 = R.select0 c R.rule01 refl
    c1 = PCRA.applySelected historicalSystem s0
    k0 : Judgment.naturalNumber I.zeroWord Finite.∈Context c1
    k0 = Closure.certifiedConclusionAvailable c s0
    s1 = R.select1 c1 (R.rule02 I.zeroWord)
      (Judgment.naturalNumber I.zeroWord) refl k0
    c2 = PCRA.applySelected historicalSystem s1
    k0' : Judgment.naturalNumber I.zeroWord Finite.∈Context c2
    k0' = Closure.certifiedStepPreservesPriorFormula c1 s1 _ k0
    k1 : Judgment.naturalNumber I.oneWord Finite.∈Context c2
    k1 = Closure.certifiedConclusionAvailable c1 s1
    sm = Rule34.selectRule4 c2 I.zeroWord I.oneWord k0' k1

emptyTupleProducer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c
    (Judgment.distinctVariableTuple I.zeroWord I.emptyWord)
emptyTupleProducer c = Producer.singleStepProducer (Rule83.selectRule831 c) refl

falsePredicateProducer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c
    (Judgment.predicateSchema I.zeroWord I.falsumWord)
falsePredicateProducer c =
  Producer.certifiedHistoricalConclusionProducer
    (PCRA.choose s0 PCRA.done) sp refl PCRA.done
  where
    s0 = R.select0 c R.rule01 refl
    c1 = PCRA.applySelected historicalSystem s0
    k0 = Closure.certifiedConclusionAvailable c s0
    sp = R.select1 c1 (R.rule913 I.zeroWord)
      (Judgment.naturalNumber I.zeroWord) refl k0

truePredicateProducer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c
    (Judgment.predicateSchema I.zeroWord I.verumWord)
truePredicateProducer c =
  Producer.certifiedHistoricalConclusionProducer
    (PCRA.choose s0 PCRA.done) sp refl PCRA.done
  where
    s0 = R.select0 c R.rule01 refl
    c1 = PCRA.applySelected historicalSystem s0
    k0 = Closure.certifiedConclusionAvailable c s0
    sp = R.select1 c1 (R.rule912 I.zeroWord)
      (Judgment.naturalNumber I.zeroWord) refl k0

noPredTrueProducer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c
    (Judgment.assertionSchemaNoPredicateQuantification I.trueAssertion)
noPredTrueProducer c =
  Producer.certifiedHistoricalConclusionProducer prefix s941 refl PCRA.done
  where
    s0 = R.select0 c R.rule01 refl
    c1 = PCRA.applySelected historicalSystem s0
    k0 = Closure.certifiedConclusionAvailable c s0
    s912 = R.select1 c1 (R.rule912 I.zeroWord)
      (Judgment.naturalNumber I.zeroWord) refl k0
    c2 = PCRA.applySelected historicalSystem s912
    pTrue = Closure.certifiedConclusionAvailable c1 s912
    s61 = R.select0 c2 R.rule61 refl
    c3 = PCRA.applySelected historicalSystem s61
    tuple0 = Closure.certifiedConclusionAvailable c2 s61
    pTrue' = Closure.certifiedStepPreservesPriorFormula c2 s61 _ pTrue
    s941 = R.select2 c3 (R.rule941 I.zeroWord I.emptyWord I.verumWord)
      (Judgment.termTuple I.zeroWord I.emptyWord)
      (Judgment.predicateSchema I.zeroWord I.verumWord)
      refl tuple0 pTrue'
    prefix = PCRA.choose s0 (PCRA.choose s912 (PCRA.choose s61 PCRA.done))

p07Producer : (c : Context) →
  Judgment.assertionSchemaNoPredicateQuantification I.trueAssertion Finite.∈Context c →
  Producer.CertifiedHistoricalConclusionProducer c
    (Judgment.assertionSchema I.falseAssertion)
p07Producer c noPredTrue =
  Producer.certifiedHistoricalConclusionProducer prefix s921 refl PCRA.done
  where
    s0 = R.select0 c R.rule01 refl
    c1 = PCRA.applySelected historicalSystem s0
    k0 = Closure.certifiedConclusionAvailable c s0
    s913 = R.select1 c1 (R.rule913 I.zeroWord)
      (Judgment.naturalNumber I.zeroWord) refl k0
    c2 = PCRA.applySelected historicalSystem s913
    pFalse = Closure.certifiedConclusionAvailable c1 s913
    s61 = R.select0 c2 R.rule61 refl
    c3 = PCRA.applySelected historicalSystem s61
    tuple0 = Closure.certifiedConclusionAvailable c2 s61
    pFalse' = Closure.certifiedStepPreservesPriorFormula c2 s61 _ pFalse
    s921 = R.select2 c3 (R.rule921 I.zeroWord I.emptyWord I.falsumWord)
      (Judgment.termTuple I.zeroWord I.emptyWord)
      (Judgment.predicateSchema I.zeroWord I.falsumWord)
      refl tuple0 pFalse'
    prefix = PCRA.choose s0 (PCRA.choose s913 (PCRA.choose s61 PCRA.done))

freshEmptyProducer : (c : Context) → (word : Signature.WordTerm) →
  Producer.CertifiedHistoricalConclusionProducer c
    (Judgment.freeForSyntax I.emptyWord word)
freshEmptyProducer c word =
  Producer.singleStepProducer (Rule8112.selectRule8113 c word) refl

fusionEmptyProducer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c
    (Judgment.juxtapositionResult I.emptyWord I.emptyWord I.emptyWord)
fusionEmptyProducer c =
  Producer.certifiedHistoricalConclusionProducer
    (PCRA.choose s61 PCRA.done) s71 refl PCRA.done
  where
    s61 = R.select0 c R.rule61 refl
    c1 = PCRA.applySelected historicalSystem s61
    tuple0 = Closure.certifiedConclusionAvailable c s61
    s71 = Rule7.selectRule71 c1 I.zeroWord I.emptyWord tuple0

abbrev16Producer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c (Later.premise16 I.canonicalLater)
abbrev16Producer c = Producer.singleStepProducer (Rule10.selectRule101 c I.body16) refl

abbrev17Producer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c (Later.premise17 I.canonicalLater)
abbrev17Producer c = Producer.singleStepProducer (Rule10.selectRule101 c I.body17) refl

abbrev26Producer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c (Later.premise26 I.canonicalLater)
abbrev26Producer c = Producer.singleStepProducer (Rule10.selectRule101 c I.body26) refl

------------------------------------------------------------------------
-- Premise 9: mark0 is fresh for F (falsum verum).
------------------------------------------------------------------------

p09Producer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c (Later.premise09 I.canonicalLater)
p09Producer c =
  Producer.certifiedHistoricalConclusionProducer prefix sFull refl PCRA.done
  where
    s0 = R.select0 c R.rule01 refl
    c1 = PCRA.applySelected historicalSystem s0
    k0 = Closure.certifiedConclusionAvailable c s0
    sm = Rule34.selectRule4 c1 I.zeroWord I.zeroWord k0 k0
    c2 = PCRA.applySelected historicalSystem sm
    mark = Closure.certifiedConclusionAvailable c1 sm
    sE = R.select1 c2 (R.rule8118 I.zeroWord I.mark0) _ refl mark
    c3 = PCRA.applySelected historicalSystem sE
    fE = Closure.certifiedConclusionAvailable c2 sE
    mark3 = Closure.certifiedStepPreservesPriorFormula c2 sE _ mark
    sV = R.select1 c3 (R.rule8122 I.zeroWord I.mark0) _ refl mark3
    c4 = PCRA.applySelected historicalSystem sV
    fV = Closure.certifiedConclusionAvailable c3 sV
    fE4 = Closure.certifiedStepPreservesPriorFormula c3 sV _ fE
    mark4 = Closure.certifiedStepPreservesPriorFormula c3 sV _ mark3
    sF = R.select1 c4 (R.rule8123 I.zeroWord I.mark0) _ refl mark4
    c5 = PCRA.applySelected historicalSystem sF
    fF = Closure.certifiedConclusionAvailable c4 sF
    fV5 = Closure.certifiedStepPreservesPriorFormula c4 sF _ fV
    fE5 = Closure.certifiedStepPreservesPriorFormula c4 sF _ fE4
    sT = Fresh.selectRule810 c5 I.mark0 I.verumWord I.emptyWord fV5 fE5
    c6 = PCRA.applySelected historicalSystem sT
    fT = Closure.certifiedConclusionAvailable c5 sT
    fF6 = Closure.certifiedStepPreservesPriorFormula c5 sT _ fF
    fV6 = Closure.certifiedStepPreservesPriorFormula c5 sT _ fV5
    sFV = Fresh.selectRule810 c6 I.mark0 I.falsumWord I.verumWord fF6 fV6
    c7 = PCRA.applySelected historicalSystem sFV
    fFV = Closure.certifiedConclusionAvailable c6 sFV
    fT7 = Closure.certifiedStepPreservesPriorFormula c6 sFV _ fT
    sFull = Fresh.selectRule810 c7 I.mark0 I.falseAssertion
      (I.juxtapose I.falsumWord I.verumWord) fT7 fFV
    prefix = PCRA.choose s0
      (PCRA.choose sm
        (PCRA.choose sE
          (PCRA.choose sV
            (PCRA.choose sF
              (PCRA.choose sT (PCRA.choose sFV PCRA.done))))))

------------------------------------------------------------------------
-- Premises 21/22 and direct identity II premises 24/25.
------------------------------------------------------------------------

p21Producer : (c : Context) →
  Producer.CertifiedHistoricalConclusionProducer c (Later.premise21 I.canonicalLater)
p21Producer c =
  Producer.certifiedHistoricalConclusionProducer
    (PCRA.choose s0 (PCRA.choose s11 PCRA.done)) sJ refl PCRA.done
  where
    s0 = R.select0 c R.rule01 refl
    c1 = PCRA.applySelected historicalSystem s0
    k0 = Closure.certifiedConclusionAvailable c s0
    s11 = R.select1 c1 (R.rule11 I.zeroWord)
      (Judgment.naturalNumber I.zeroWord) refl k0
    c2 = PCRA.applySelected historicalSystem s11
    neq = Closure.certifiedConclusionAvailable c1 s11
    k0' = Closure.certifiedStepPreservesPriorFormula c1 s11 _ k0
    sJ = Rule8117.selectRule8117 c2 I.zeroWord I.zeroWord I.oneWord k0' neq

freshMark1ContextProducer :
  (c : Context) →
  Later.premise09 I.canonicalLater Finite.∈Context c →
  Producer.CertifiedHistoricalConclusionProducer c (Later.premise22 I.canonicalLater)
freshMark1ContextProducer c p09 =
  Producer.certifiedHistoricalConclusionProducer prefix sPair refl PCRA.done
  where
    s0 = R.select0 c R.rule01 refl
    c1 = PCRA.applySelected historicalSystem s0
    k0 = Closure.certifiedConclusionAvailable c s0
    s1 = R.select1 c1 (R.rule02 I.zeroWord) _ refl k0
    c2 = PCRA.applySelected historicalSystem s1
    k0' = Closure.certifiedStepPreservesPriorFormula c1 s1 _ k0
    k1 = Closure.certifiedConclusionAvailable c1 s1
    sm = Rule34.selectRule4 c2 I.zeroWord I.oneWord k0' k1
    c3 = PCRA.applySelected historicalSystem sm
    mark = Closure.certifiedConclusionAvailable c2 sm
    sE = R.select1 c3 (R.rule8118 I.zeroWord I.mark1) _ refl mark
    c4 = PCRA.applySelected historicalSystem sE
    fE = Closure.certifiedConclusionAvailable c3 sE
    mark4 = Closure.certifiedStepPreservesPriorFormula c3 sE _ mark
    sV = R.select1 c4 (R.rule8122 I.zeroWord I.mark1) _ refl mark4
    c5 = PCRA.applySelected historicalSystem sV
    fV = Closure.certifiedConclusionAvailable c4 sV
    fE5 = Closure.certifiedStepPreservesPriorFormula c4 sV _ fE
    mark5 = Closure.certifiedStepPreservesPriorFormula c4 sV _ mark4
    sF = R.select1 c5 (R.rule8123 I.zeroWord I.mark1) _ refl mark5
    c6 = PCRA.applySelected historicalSystem sF
    fF = Closure.certifiedConclusionAvailable c5 sF
    fV6 = Closure.certifiedStepPreservesPriorFormula c5 sF _ fV
    fE6 = Closure.certifiedStepPreservesPriorFormula c5 sF _ fE5
    sFalse = Fresh.selectRule810 c6 I.mark1 I.falsumWord I.emptyWord fF fE6
    c7 = PCRA.applySelected historicalSystem sFalse
    fFalse = Closure.certifiedConclusionAvailable c6 sFalse
    fV7 = Closure.certifiedStepPreservesPriorFormula c6 sFalse _ fV6
    fE7 = Closure.certifiedStepPreservesPriorFormula c6 sFalse _ fE6
    sTrue = Fresh.selectRule810 c7 I.mark1 I.verumWord I.emptyWord fV7 fE7
    c8 = PCRA.applySelected historicalSystem sTrue
    fTrue = Closure.certifiedConclusionAvailable c7 sTrue
    fFalse8 = Closure.certifiedStepPreservesPriorFormula c7 sTrue _ fFalse
    sFV = Fresh.selectRule810 c8 I.mark1 I.falsumWord I.verumWord
      (Closure.certifiedStepPreservesPriorFormula c7 sTrue _ fV7)
      (Closure.certifiedStepPreservesPriorFormula c7 sTrue _ fV7)
    -- Rebuild the required (falsum,verum) context with the actual two receipts.
    -- The first argument below is replaced immediately by a source-correct step.
    -- We keep a separate selected value to avoid conflating falsum and verum.
    sFV' = Fresh.selectRule810 c8 I.mark1 I.falsumWord I.verumWord
      (Closure.certifiedStepPreservesPriorFormula c7 sTrue _
        (Closure.certifiedStepPreservesPriorFormula c6 sFalse _ fF))
      (Closure.certifiedStepPreservesPriorFormula c7 sTrue _ fV7)
    c9 = PCRA.applySelected historicalSystem sFV'
    fFV = Closure.certifiedConclusionAvailable c8 sFV'
    fFalse9 = Closure.certifiedStepPreservesPriorFormula c8 sFV' _ fFalse8
    sFull = Fresh.selectRule810 c9 I.mark1 I.falseAssertion
      (I.juxtapose I.falsumWord I.verumWord) fFalse9 fFV
    c10 = PCRA.applySelected historicalSystem sFull
    m1Full = Closure.certifiedConclusionAvailable c9 sFull
    p09Now = Closure.certifiedTracePreservesPriorFormula prefixToFull _ p09
    sPair = Rule8112.selectRule8112 c10 I.mark0 I.mark1 I.context09 p09Now m1Full
    prefixToFull = PCRA.choose s0
      (PCRA.choose s1
        (PCRA.choose sm
          (PCRA.choose sE
            (PCRA.choose sV
              (PCRA.choose sF
                (PCRA.choose sFalse
                  (PCRA.choose sTrue (PCRA.choose sFV' (PCRA.choose sFull PCRA.done)))))))))
    prefix = prefixToFull

identityIIProducer :
  (c : Context) → (replacement : Signature.WordTerm) →
  Producer.CertifiedHistoricalConclusionProducer c
    (Judgment.substitution
      (I.juxtapose I.mark0 I.emptyWord)
      I.trueAssertion replacement I.trueAssertion)
identityIIProducer c replacement =
  Producer.certifiedHistoricalConclusionProducer prefix sII refl PCRA.done
  where
    s0 = R.select0 c R.rule01 refl
    c1 = PCRA.applySelected historicalSystem s0
    k0 = Closure.certifiedConclusionAvailable c s0
    sm = Rule34.selectRule4 c1 I.zeroWord I.zeroWord k0 k0
    c2 = PCRA.applySelected historicalSystem sm
    mark = Closure.certifiedConclusionAvailable c1 sm
    sE = R.select1 c2 (R.rule8118 I.zeroWord I.mark0) _ refl mark
    c3 = PCRA.applySelected historicalSystem sE
    fE = Closure.certifiedConclusionAvailable c2 sE
    mark3 = Closure.certifiedStepPreservesPriorFormula c2 sE _ mark
    sV = R.select1 c3 (R.rule8122 I.zeroWord I.mark0) _ refl mark3
    c4 = PCRA.applySelected historicalSystem sV
    fV = Closure.certifiedConclusionAvailable c3 sV
    fE4 = Closure.certifiedStepPreservesPriorFormula c3 sV _ fE
    sT = Fresh.selectRule810 c4 I.mark0 I.verumWord I.emptyWord fV fE4
    c5 = PCRA.applySelected historicalSystem sT
    fT = Closure.certifiedConclusionAvailable c4 sT
    sEmptyT = Rule8112.selectRule8113 c5 I.trueAssertion
    c6 = PCRA.applySelected historicalSystem sEmptyT
    eT = Closure.certifiedConclusionAvailable c5 sEmptyT
    mT = Closure.certifiedStepPreservesPriorFormula c5 sEmptyT _ fT
    sPairFresh = Rule8112.selectRule8112 c6 I.mark0 I.emptyWord I.trueAssertion mT eT
    c7 = PCRA.applySelected historicalSystem sPairFresh
    pairFresh = Closure.certifiedConclusionAvailable c6 sPairFresh
    sII = R.select1 c7
      (Subst.rule8-2-2 (I.juxtapose I.mark0 I.emptyWord) I.trueAssertion replacement)
      (Judgment.freeForSyntax (I.juxtapose I.mark0 I.emptyWord) I.trueAssertion)
      refl pairFresh
    prefix = PCRA.choose s0
      (PCRA.choose sm
        (PCRA.choose sE
          (PCRA.choose sV
            (PCRA.choose sT
              (PCRA.choose sEmptyT (PCRA.choose sPairFresh PCRA.done))))))

------------------------------------------------------------------------
-- Canonical producer blocks from the empty derivation context.
------------------------------------------------------------------------

formation : Formation.FormationProducerChain [] I.canonicalFirstSeven I.canonicalLater
formation = Formation.formationProducerChain p01 p02 p03 p04 p05 p06 p07
  where
    p01 = p01Producer []
    p02 = mark0Producer (Producer.producerTarget p01)
    p03 = emptyTupleProducer (Producer.producerTarget p02)
    p04 = falsePredicateProducer (Producer.producerTarget p03)
    p05 = truePredicateProducer (Producer.producerTarget p04)
    p06 = noPredTrueProducer (Producer.producerTarget p05)
    p07 = p07Producer (Producer.producerTarget p06) (Producer.producedAtTarget p06)

shared : Shared.Shared1015ProducerChain
  (Formation.formationTarget formation) I.canonicalFirstSeven I.canonicalLater
shared = Shared.shared1015ProducerChain p10 p11 p12 p13 p14 p15
  where
    p10 = emptyTupleProducer (Formation.formationTarget formation)
    p11 = emptyTupleProducer (Producer.producerTarget p10)
    p12 = freshEmptyProducer (Producer.producerTarget p11) I.emptyWord
    p13 = freshEmptyProducer (Producer.producerTarget p12) I.falseAssertion
    p14 = freshEmptyProducer (Producer.producerTarget p13) I.context14
    p15 = fusionEmptyProducer (Producer.producerTarget p14)

induction : Induction.InductionScaffoldProducerChain
  (Shared.sharedTarget shared) I.canonicalLater
induction = Induction.inductionScaffoldProducerChain p08 p09 p16 p17
  where
    p08 = mark0Producer (Shared.sharedTarget shared)
    p09 = p09Producer (Producer.producerTarget p08)
    p16 = abbrev16Producer (Producer.producerTarget p09)
    p17 = abbrev17Producer (Producer.producerTarget p16)

independence : Independence.IndependenceScaffoldProducerChain
  (Induction.inductionScaffoldTarget induction) I.canonicalLater
independence = Independence.independenceScaffoldProducerChain
  p19 p20 p21 p22 p23 p24 p25 p26
  where
    start = Induction.inductionScaffoldTarget induction
    p19 = mark0Producer start
    p20 = mark1Producer (Producer.producerTarget p19)
    p21 = p21Producer (Producer.producerTarget p20)

    p09Start : Later.premise09 I.canonicalLater Finite.∈Context start
    p09Start = Induction.p09AtTarget induction
    p09After19 = Closure.certifiedTracePreservesPriorFormula
      (Producer.producerTrace p19) _ p09Start
    p09After20 = Closure.certifiedTracePreservesPriorFormula
      (Producer.producerTrace p20) _ p09After19
    p09After21 = Closure.certifiedTracePreservesPriorFormula
      (Producer.producerTrace p21) _ p09After20

    p22 = freshMark1ContextProducer (Producer.producerTarget p21) p09After21
    p23 = freshEmptyProducer (Producer.producerTarget p22) I.trueAssertion
    p24 = identityIIProducer (Producer.producerTarget p23)
      (I.juxtapose I.mark0 I.emptyWord)
    p25 = identityIIProducer (Producer.producerTarget p24)
      (I.juxtapose I.mark1 I.emptyWord)
    p26 = abbrev26Producer (Producer.producerTarget p25)

canonicalScaffold : Source.SourceExactScaffoldInputs [] I.canonicalFirstSeven I.canonicalLater
canonicalScaffold = Source.sourceExactScaffoldInputs formation shared induction independence

record Wette1969Rule915ZeroArityFalsumScaffoldBoundary : Set where
  constructor wette1969Rule915ZeroArityFalsumScaffoldBoundary
  field
    concreteSourceExactScaffoldStartsFromEmptyContext : Bool
    concreteSourceExactScaffoldStartsFromEmptyContextIsTrue : concreteSourceExactScaffoldStartsFromEmptyContext ≡ true
    everyNonMajorSlotIsProducedByCertifiedHistoricalTrace : Bool
    everyNonMajorSlotIsProducedByCertifiedHistoricalTraceIsTrue : everyNonMajorSlotIsProducedByCertifiedHistoricalTrace ≡ true
    emptyTupleAndFreshnessCollapseUsedOnlyWhereSourceRulesPermit : Bool
    emptyTupleAndFreshnessCollapseUsedOnlyWhereSourceRulesPermitIsTrue : emptyTupleAndFreshnessCollapseUsedOnlyWhereSourceRulesPermit ≡ true
    premises24And25UseDirectHistorical822IdentitySubstitution : Bool
    premises24And25UseDirectHistorical822IdentitySubstitutionIsTrue : premises24And25UseDirectHistorical822IdentitySubstitution ≡ true

canonicalWette1969Rule915ZeroArityFalsumScaffoldBoundary :
  Wette1969Rule915ZeroArityFalsumScaffoldBoundary
canonicalWette1969Rule915ZeroArityFalsumScaffoldBoundary =
  wette1969Rule915ZeroArityFalsumScaffoldBoundary true refl true refl true refl true refl
