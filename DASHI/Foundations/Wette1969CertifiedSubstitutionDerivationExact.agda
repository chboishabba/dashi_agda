module DASHI.Foundations.Wette1969CertifiedSubstitutionDerivationExact where

------------------------------------------------------------------------
-- CERTIFIED COMPOSITIONAL WETTE SUBSTITUTION DERIVATIONS
--
-- This is the execution layer over Wette1969SubstitutionRuleSpineExact.
-- Rather than inventing a total meta-level substitution function, it builds
-- historical II judgements by certified applications of Wette's own 8.2 rules.
-- Recursive constructor steps consume earlier generated II conclusions at the
-- actual reached finite context; binder freshness evidence is transported to
-- that same reached context before 8.2.9/10/11 is applied.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Data.Fin as Fin

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969SubstitutionRuleSpineExact as Spine
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

historicalSystem = Closure.historicalApplicationSystem

record CertifiedSubstitutionDerivation
    (context : Context)
    (substituend source replacement result : WordTerm) : Set₁ where
  constructor certifiedSubstitutionDerivation
  field
    trace : PCRA.CertifiedRuleTrace historicalSystem context
    resultAvailable :
      Judgment.substitution substituend source replacement result
        Finite.∈Context
        (PCRA.runCertifiedTrace historicalSystem trace)

open CertifiedSubstitutionDerivation public

targetContext :
  {context : Context} → {s u r v : WordTerm} →
  CertifiedSubstitutionDerivation context s u r v → Context
targetContext derivation = PCRA.runCertifiedTrace historicalSystem (trace derivation)

------------------------------------------------------------------------
-- One-premise base/unchanged producers.
------------------------------------------------------------------------

onePremiseHold :
  (context : Context) →
  (rule : RuleBody.HistoricalRuleBody) →
  RuleBody.premiseCount rule ≡ 1 →
  (premise : Signature.Formula) →
  RuleBody.premises rule Finite.∈Context context → Set
onePremiseHold context rule count premise impossible = ⊤

variableBase :
  (context : Context) →
  (variable replacement : WordTerm) →
  Judgment.naturalVariable variable Finite.∈Context context →
  CertifiedSubstitutionDerivation context variable variable replacement replacement
variableBase context variable replacement variableEvidence =
  certifiedSubstitutionDerivation
    (PCRA.choose selected PCRA.done)
    Finite.here
  where
    premises :
      Historical.PremisesHold
        Finite.finiteHistoricalContextSystem context
        (Spine.rule8-2-1 variable replacement)
    premises Fin.zero = variableEvidence

    selected =
      PCRA.selectedRuleApplication
        (Spine.rule8-2-1 variable replacement)
        (Historical.certifyHistoricalRule
          Finite.finiteHistoricalContextSystem context
          (Spine.rule8-2-1 variable replacement)
          premises)

predicateMarkBase :
  (context : Context) →
  (arity mark replacement : WordTerm) →
  Judgment.predicateMarkArity arity mark Finite.∈Context context →
  CertifiedSubstitutionDerivation context mark mark replacement replacement
predicateMarkBase context arity mark replacement markEvidence =
  certifiedSubstitutionDerivation
    (PCRA.choose selected PCRA.done)
    Finite.here
  where
    premises :
      Historical.PremisesHold
        Finite.finiteHistoricalContextSystem context
        (Spine.rule8-2-12 arity mark replacement)
    premises Fin.zero = markEvidence

    selected =
      PCRA.selectedRuleApplication
        (Spine.rule8-2-12 arity mark replacement)
        (Historical.certifyHistoricalRule
          Finite.finiteHistoricalContextSystem context
          (Spine.rule8-2-12 arity mark replacement)
          premises)

unchangedUnderFreshness :
  (context : Context) →
  (substituend source replacement : WordTerm) →
  Judgment.freeForSyntax substituend source Finite.∈Context context →
  CertifiedSubstitutionDerivation context substituend source replacement source
unchangedUnderFreshness context substituend source replacement freshness =
  certifiedSubstitutionDerivation
    (PCRA.choose selected PCRA.done)
    Finite.here
  where
    premises :
      Historical.PremisesHold
        Finite.finiteHistoricalContextSystem context
        (Spine.rule8-2-2 substituend source replacement)
    premises Fin.zero = freshness

    selected =
      PCRA.selectedRuleApplication
        (Spine.rule8-2-2 substituend source replacement)
        (Historical.certifyHistoricalRule
          Finite.finiteHistoricalContextSystem context
          (Spine.rule8-2-2 substituend source replacement)
          premises)

------------------------------------------------------------------------
-- Successor congruence: generated body II becomes the sole premise of 8.2.3.
------------------------------------------------------------------------

successorCongruence :
  {context : Context} →
  {substituend source replacement result : WordTerm} →
  CertifiedSubstitutionDerivation context substituend source replacement result →
  CertifiedSubstitutionDerivation
    context
    substituend
    (Spine.unary Signature.successorFunctor source)
    replacement
    (Spine.unary Signature.successorFunctor result)
successorCongruence derivation =
  certifiedSubstitutionDerivation
    (PCRA.appendCertifiedTrace (trace derivation)
      (PCRA.choose selected PCRA.done))
    Finite.here
  where
    current = targetContext derivation

    premises :
      Historical.PremisesHold
        Finite.finiteHistoricalContextSystem current
        (Spine.rule8-2-3 _ _ _ _)
    premises Fin.zero = resultAvailable derivation

    selected =
      PCRA.selectedRuleApplication
        (Spine.rule8-2-3 _ _ _ _)
        (Historical.certifyHistoricalRule
          Finite.finiteHistoricalContextSystem current
          (Spine.rule8-2-3 _ _ _ _)
          premises)

------------------------------------------------------------------------
-- Binary congruence constructors 8.2.4--7.
------------------------------------------------------------------------

data BinarySubstitutionConstructor : Set where
  juxtorCase implicationCase conjunctionCase disjunctionCase :
    BinarySubstitutionConstructor

binaryFunctor : BinarySubstitutionConstructor → Signature.HistoricalFunctor
binaryFunctor juxtorCase = Signature.juxtapositionFunctor
binaryFunctor implicationCase = Signature.implicationFunctor
binaryFunctor conjunctionCase = Signature.conjunctionFunctor
binaryFunctor disjunctionCase = Signature.disjunctionFunctor

binaryRuleItem : BinarySubstitutionConstructor → Nat
binaryRuleItem juxtorCase = 4
binaryRuleItem implicationCase = 5
binaryRuleItem conjunctionCase = 6
binaryRuleItem disjunctionCase = 7

binaryCongruence :
  {context : Context} →
  {substituend left right replacement leftResult rightResult : WordTerm} →
  (constructor : BinarySubstitutionConstructor) →
  (leftDerivation :
    CertifiedSubstitutionDerivation
      context substituend left replacement leftResult) →
  (rightDerivation :
    CertifiedSubstitutionDerivation
      (targetContext leftDerivation)
      substituend right replacement rightResult) →
  CertifiedSubstitutionDerivation
    context
    substituend
    (Spine.binary (binaryFunctor constructor) left right)
    replacement
    (Spine.binary (binaryFunctor constructor) leftResult rightResult)
binaryCongruence
  {substituend = substituend} {left} {right} {replacement}
  {leftResult} {rightResult}
  constructor leftDerivation rightDerivation =
  certifiedSubstitutionDerivation
    (PCRA.appendCertifiedTrace
      (trace leftDerivation)
      (PCRA.appendCertifiedTrace
        (trace rightDerivation)
        (PCRA.choose selected PCRA.done)))
    Finite.here
  where
    current = targetContext rightDerivation

    leftAvailable :
      Judgment.substitution substituend left replacement leftResult
        Finite.∈Context current
    leftAvailable =
      Closure.certifiedTracePreservesPriorFormula
        (trace rightDerivation)
        (Judgment.substitution substituend left replacement leftResult)
        (resultAvailable leftDerivation)

    rule =
      Spine.binaryCongruenceRule
        (binaryRuleItem constructor)
        (binaryFunctor constructor)
        substituend left right replacement leftResult rightResult

    premises :
      Historical.PremisesHold Finite.finiteHistoricalContextSystem current rule
    premises Fin.zero = leftAvailable
    premises (Fin.suc Fin.zero) = resultAvailable rightDerivation

    selected =
      PCRA.selectedRuleApplication rule
        (Historical.certifyHistoricalRule
          Finite.finiteHistoricalContextSystem current rule premises)

------------------------------------------------------------------------
-- Binder congruence constructors 8.2.9--11.
------------------------------------------------------------------------

data BinderSubstitutionConstructor : Set where
  particularizerCase generalizerCase recursorCase : BinderSubstitutionConstructor

binderFunctor : BinderSubstitutionConstructor → Signature.HistoricalFunctor
binderFunctor particularizerCase = Signature.particularizationFunctor
binderFunctor generalizerCase = Signature.generalizationFunctor
binderFunctor recursorCase = Signature.recursionFunctor

binderRuleItem : BinderSubstitutionConstructor → Nat
binderRuleItem particularizerCase = 9
binderRuleItem generalizerCase = 10
binderRuleItem recursorCase = 11

binderCongruence :
  {context : Context} →
  {binder substituend body replacement result : WordTerm} →
  (constructor : BinderSubstitutionConstructor) →
  Judgment.freeForSyntax binder replacement Finite.∈Context context →
  Judgment.freeForSyntax binder substituend Finite.∈Context context →
  (bodyDerivation :
    CertifiedSubstitutionDerivation
      context substituend body replacement result) →
  CertifiedSubstitutionDerivation
    context
    substituend
    (Spine.binary (binderFunctor constructor) binder body)
    replacement
    (Spine.binary (binderFunctor constructor) binder result)
binderCongruence
  {context} {binder} {substituend} {body} {replacement} {result}
  constructor replacementFresh substituendFresh bodyDerivation =
  certifiedSubstitutionDerivation
    (PCRA.appendCertifiedTrace
      (trace bodyDerivation)
      (PCRA.choose selected PCRA.done))
    Finite.here
  where
    current = targetContext bodyDerivation

    replacementFreshNow :
      Judgment.freeForSyntax binder replacement Finite.∈Context current
    replacementFreshNow =
      Closure.certifiedTracePreservesPriorFormula
        (trace bodyDerivation)
        (Judgment.freeForSyntax binder replacement)
        replacementFresh

    substituendFreshNow :
      Judgment.freeForSyntax binder substituend Finite.∈Context current
    substituendFreshNow =
      Closure.certifiedTracePreservesPriorFormula
        (trace bodyDerivation)
        (Judgment.freeForSyntax binder substituend)
        substituendFresh

    rule =
      Spine.binderCongruenceRule
        (binderRuleItem constructor)
        (binderFunctor constructor)
        binder substituend body replacement result

    premises :
      Historical.PremisesHold Finite.finiteHistoricalContextSystem current rule
    premises Fin.zero = replacementFreshNow
    premises (Fin.suc Fin.zero) = substituendFreshNow
    premises (Fin.suc (Fin.suc Fin.zero)) = resultAvailable bodyDerivation

    selected =
      PCRA.selectedRuleApplication rule
        (Historical.certifyHistoricalRule
          Finite.finiteHistoricalContextSystem current rule premises)

recursorCongruence = binderCongruence recursorCase

record Wette1969CertifiedSubstitutionDerivationBoundary : Set where
  constructor wette1969CertifiedSubstitutionDerivationBoundary
  field
    historicalIIJudgementsNowComposeByCertified82Rules : Bool
    historicalIIJudgementsNowComposeByCertified82RulesIsTrue :
      historicalIIJudgementsNowComposeByCertified82Rules ≡ true
    binarySubderivationsSequenceAtActualReachedContexts : Bool
    binarySubderivationsSequenceAtActualReachedContextsIsTrue :
      binarySubderivationsSequenceAtActualReachedContexts ≡ true
    binderFreshnessTransportedToBodyDerivationTarget : Bool
    binderFreshnessTransportedToBodyDerivationTargetIsTrue :
      binderFreshnessTransportedToBodyDerivationTarget ≡ true
    recursorSubstitutionNowHasComposableHistoricalDerivationConstructor : Bool
    recursorSubstitutionNowHasComposableHistoricalDerivationConstructorIsTrue :
      recursorSubstitutionNowHasComposableHistoricalDerivationConstructor ≡ true
    compositionalDerivationIsAlreadyTotalSubstitutionDecisionProcedure : Bool
    compositionalDerivationIsAlreadyTotalSubstitutionDecisionProcedureIsFalse :
      compositionalDerivationIsAlreadyTotalSubstitutionDecisionProcedure ≡ false

canonicalWette1969CertifiedSubstitutionDerivationBoundary :
  Wette1969CertifiedSubstitutionDerivationBoundary
canonicalWette1969CertifiedSubstitutionDerivationBoundary =
  wette1969CertifiedSubstitutionDerivationBoundary
    true refl true refl true refl true refl false refl
