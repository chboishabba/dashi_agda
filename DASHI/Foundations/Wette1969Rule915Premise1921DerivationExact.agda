module DASHI.Foundations.Wette1969Rule915Premise1921DerivationExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5 PREMISES 19--21: FRESH PREDICATE-MARK PAIR
--
-- Premises 19/20 require two V-place predicate marks W4/W5.  Premise 21 states
-- their mutual J-freshness.  Rule 4 produces each canonical mark from natural
-- arity/index evidence and rule 8.1.17 derives freshness for distinct indices.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969ObjectVariableMarkWordsExact as ObjectSyntax
import DASHI.Foundations.Wette1969Rule34ObjectProducerExact as Rule34
import DASHI.Foundations.Wette1969Rule8117PredicateMarkFreshnessExact as Rule8117
import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite
import DASHI.Foundations.Wette1969DerivationClosureExact as Closure

WordTerm = Later.WordTerm
Context = Finite.DerivationContext
historicalSystem = Closure.historicalApplicationSystem

record Premise1921Inputs
    (context : Context)
    (later : Later.Rule915LaterParameters) : Set where
  constructor premise1921Inputs
  field
    index4 : WordTerm
    index5 : WordTerm
    mark4Shape :
      Later.predicateMarkW4 later
        ≡ ObjectSyntax.predicateMarkWord (Later.arityWord later) index4
    mark5Shape :
      Later.predicateMarkW5 later
        ≡ ObjectSyntax.predicateMarkWord (Later.arityWord later) index5

    arityNatural :
      Judgment.naturalNumber (Later.arityWord later) Finite.∈Context context
    index4Natural : Judgment.naturalNumber index4 Finite.∈Context context
    index5Natural : Judgment.naturalNumber index5 Finite.∈Context context
    indicesUnequal : Judgment.unequal index4 index5 Finite.∈Context context

open Premise1921Inputs public

selectedMark4 :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  (inputs : Premise1921Inputs context later) →
  PCRA.SelectedRuleApplication historicalSystem context
selectedMark4 {context} {later} inputs =
  Rule34.selectRule4
    context (Later.arityWord later) (index4 inputs)
    (arityNatural inputs) (index4Natural inputs)

contextAfterMark4 :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  Premise1921Inputs context later → Context
contextAfterMark4 inputs =
  PCRA.applySelected historicalSystem (selectedMark4 inputs)

selectedMark5 :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  (inputs : Premise1921Inputs context later) →
  PCRA.SelectedRuleApplication historicalSystem (contextAfterMark4 inputs)
selectedMark5 {later = later} inputs =
  Rule34.selectRule4
    (contextAfterMark4 inputs)
    (Later.arityWord later)
    (index5 inputs)
    (Closure.certifiedStepPreservesPriorFormula
      _ (selectedMark4 inputs) _ (arityNatural inputs))
    (Closure.certifiedStepPreservesPriorFormula
      _ (selectedMark4 inputs) _ (index5Natural inputs))

contextAfterMark5 :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  Premise1921Inputs context later → Context
contextAfterMark5 inputs =
  PCRA.applySelected historicalSystem (selectedMark5 inputs)

selectedFreshMarks :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  (inputs : Premise1921Inputs context later) →
  PCRA.SelectedRuleApplication historicalSystem (contextAfterMark5 inputs)
selectedFreshMarks {later = later} inputs =
  Rule8117.selectRule8117
    (contextAfterMark5 inputs)
    (Later.arityWord later)
    (index4 inputs)
    (index5 inputs)
    arityAtMark5
    unequalAtMark5
  where
    arityAtMark4 =
      Closure.certifiedStepPreservesPriorFormula
        _ (selectedMark4 inputs) _ (arityNatural inputs)
    arityAtMark5 =
      Closure.certifiedStepPreservesPriorFormula
        _ (selectedMark5 inputs) _ arityAtMark4

    unequalAtMark4 =
      Closure.certifiedStepPreservesPriorFormula
        _ (selectedMark4 inputs) _ (indicesUnequal inputs)
    unequalAtMark5 =
      Closure.certifiedStepPreservesPriorFormula
        _ (selectedMark5 inputs) _ unequalAtMark4

premise1921Trace :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  (inputs : Premise1921Inputs context later) →
  PCRA.CertifiedRuleTrace historicalSystem context
premise1921Trace inputs =
  PCRA.choose
    (selectedMark4 inputs)
    (PCRA.choose
      (selectedMark5 inputs)
      (PCRA.choose (selectedFreshMarks inputs) PCRA.done))

premise1921Target :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  Premise1921Inputs context later → Context
premise1921Target inputs =
  PCRA.runCertifiedTrace historicalSystem (premise1921Trace inputs)

premise19Available :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  (inputs : Premise1921Inputs context later) →
  Later.premise19 later Finite.∈Context premise1921Target inputs
premise19Available {later = later} inputs
  rewrite mark4Shape inputs =
  Closure.certifiedTracePreservesPriorFormula
    (PCRA.choose (selectedMark5 inputs)
      (PCRA.choose (selectedFreshMarks inputs) PCRA.done))
    _
    Finite.here

premise20Available :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  (inputs : Premise1921Inputs context later) →
  Later.premise20 later Finite.∈Context premise1921Target inputs
premise20Available {later = later} inputs
  rewrite mark5Shape inputs =
  Closure.certifiedStepPreservesPriorFormula
    (contextAfterMark5 inputs)
    (selectedFreshMarks inputs)
    _
    Finite.here

premise21Available :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  (inputs : Premise1921Inputs context later) →
  Later.premise21 later Finite.∈Context premise1921Target inputs
premise21Available {later = later} inputs
  rewrite mark4Shape inputs | mark5Shape inputs = Finite.here

record Wette1969Rule915Premise1921Boundary : Set where
  constructor wette1969Rule915Premise1921Boundary
  field
    premises19And20GeneratedByHistoricalRule4 : Bool
    premises19And20GeneratedByHistoricalRule4IsTrue :
      premises19And20GeneratedByHistoricalRule4 ≡ true
    premise21GeneratedByHistoricalRule8117 : Bool
    premise21GeneratedByHistoricalRule8117IsTrue :
      premise21GeneratedByHistoricalRule8117 ≡ true
    naturalIndexAndInequalityEvidenceRemainExplicit : Bool
    naturalIndexAndInequalityEvidenceRemainExplicitIsTrue :
      naturalIndexAndInequalityEvidenceRemainExplicit ≡ true

canonicalWette1969Rule915Premise1921Boundary :
  Wette1969Rule915Premise1921Boundary
canonicalWette1969Rule915Premise1921Boundary =
  wette1969Rule915Premise1921Boundary
    true refl true refl true refl
