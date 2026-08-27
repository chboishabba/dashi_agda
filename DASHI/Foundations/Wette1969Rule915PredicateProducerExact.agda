module DASHI.Foundations.Wette1969Rule915PredicateProducerExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: PREDICATE-SCHEMA OUTPUT PRODUCER
--
-- Eduard Wette, 1969, DOI 10.1007/978-3-642-86745-3_9.
--
-- Section 1.61 states the source role unambiguously: 9.1.5 takes the variable
-- tuple x, predicate mark pi, P/R, A/C and its twenty implication-generated
-- side conditions and produces a new k-place predicate schema
--
--     CPR -1 pi x A.
--
-- The complete OCR-perfect 27 premise bodies are not yet all recovered.  This
-- module therefore fixes what is already source-exact -- address, premise count,
-- slot order and predicate-schema conclusion -- while requiring the 27 premise
-- formulae as a slot-indexed transcription parameter.  This is sufficient to
-- make an actually certified 9.1.5 application generate 9.3.24/25 premise 1,
-- without falsely promoting the remaining premise transcription.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

WordTerm = Signature.WordTerm
Formula = Signature.Formula
Context = Finite.DerivationContext

record Rule915PremiseTranscription : Set₁ where
  constructor rule915PremiseTranscription
  field
    premiseAt : Critical.Premise915 → Formula

open Rule915PremiseTranscription public

premiseVector915 : Rule915PremiseTranscription → Vec Formula 27
premiseVector915 transcription =
  premiseAt transcription Critical.p01 ∷ᵥ
  premiseAt transcription Critical.p02 ∷ᵥ
  premiseAt transcription Critical.p03 ∷ᵥ
  premiseAt transcription Critical.p04 ∷ᵥ
  premiseAt transcription Critical.p05 ∷ᵥ
  premiseAt transcription Critical.p06 ∷ᵥ
  premiseAt transcription Critical.p07 ∷ᵥ
  premiseAt transcription Critical.p08 ∷ᵥ
  premiseAt transcription Critical.p09 ∷ᵥ
  premiseAt transcription Critical.p10 ∷ᵥ
  premiseAt transcription Critical.p11 ∷ᵥ
  premiseAt transcription Critical.p12 ∷ᵥ
  premiseAt transcription Critical.p13 ∷ᵥ
  premiseAt transcription Critical.p14 ∷ᵥ
  premiseAt transcription Critical.p15 ∷ᵥ
  premiseAt transcription Critical.p16 ∷ᵥ
  premiseAt transcription Critical.p17 ∷ᵥ
  premiseAt transcription Critical.p18 ∷ᵥ
  premiseAt transcription Critical.p19 ∷ᵥ
  premiseAt transcription Critical.p20 ∷ᵥ
  premiseAt transcription Critical.p21 ∷ᵥ
  premiseAt transcription Critical.p22 ∷ᵥ
  premiseAt transcription Critical.p23 ∷ᵥ
  premiseAt transcription Critical.p24 ∷ᵥ
  premiseAt transcription Critical.p25 ∷ᵥ
  premiseAt transcription Critical.p26 ∷ᵥ
  premiseAt transcription Critical.p27 ∷ᵥ
  []ᵥ

rule9-1-5 :
  Rule915PremiseTranscription →
  WordTerm →
  WordTerm →
  RuleBody.HistoricalRuleBody
rule9-1-5 transcription arity recursivePredicate =
  RuleBody.historicalRuleBody
    Revision.rule9-1-5
    27
    (premiseVector915 transcription)
    (Judgment.predicateSchema arity recursivePredicate)

rule915HasTwentySevenPremises :
  (transcription : Rule915PremiseTranscription) →
  (arity recursivePredicate : WordTerm) →
  RuleBody.premiseCount (rule9-1-5 transcription arity recursivePredicate) ≡ 27
rule915HasTwentySevenPremises transcription arity recursivePredicate = refl

rule915ProducesPredicateSchema :
  (transcription : Rule915PremiseTranscription) →
  (arity recursivePredicate : WordTerm) →
  RuleBody.conclusion (rule9-1-5 transcription arity recursivePredicate)
    ≡ Judgment.predicateSchema arity recursivePredicate
rule915ProducesPredicateSchema transcription arity recursivePredicate = refl

selectRule915 :
  (context : Context) →
  (transcription : Rule915PremiseTranscription) →
  (arity recursivePredicate : WordTerm) →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    context
    (rule9-1-5 transcription arity recursivePredicate) →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule915 context transcription arity recursivePredicate evidence =
  PCRA.selectedRuleApplication
    (rule9-1-5 transcription arity recursivePredicate)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem
      context
      (rule9-1-5 transcription arity recursivePredicate)
      evidence)

predicateSchemaAvailableAfter915 :
  (context : Context) →
  (transcription : Rule915PremiseTranscription) →
  (arity recursivePredicate : WordTerm) →
  (evidence :
    Historical.PremisesHold
      Finite.finiteHistoricalContextSystem
      context
      (rule9-1-5 transcription arity recursivePredicate)) →
  Judgment.predicateSchema arity recursivePredicate Finite.∈Context
    (PCRA.applySelected
      (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
      (selectRule915 context transcription arity recursivePredicate evidence))
predicateSchemaAvailableAfter915 context transcription arity recursivePredicate evidence =
  Finite.here

record Wette1969Rule915PredicateProducerBoundary : Set where
  constructor wette1969Rule915PredicateProducerBoundary
  field
    rule915AddressCountAndPredicateOutputNowTyped : Bool
    rule915AddressCountAndPredicateOutputNowTypedIsTrue :
      rule915AddressCountAndPredicateOutputNowTyped ≡ true

    certified915ApplicationGeneratesPredicateSchemaPremise : Bool
    certified915ApplicationGeneratesPredicateSchemaPremiseIsTrue :
      certified915ApplicationGeneratesPredicateSchemaPremise ≡ true

    allTwentySevenPremiseBodiesNowLiteralOCRPerfect : Bool
    allTwentySevenPremiseBodiesNowLiteralOCRPerfectIsFalse :
      allTwentySevenPremiseBodiesNowLiteralOCRPerfect ≡ false

    producerTemplateAloneDischargesRule915Premises : Bool
    producerTemplateAloneDischargesRule915PremisesIsFalse :
      producerTemplateAloneDischargesRule915Premises ≡ false

canonicalWette1969Rule915PredicateProducerBoundary :
  Wette1969Rule915PredicateProducerBoundary
canonicalWette1969Rule915PredicateProducerBoundary =
  wette1969Rule915PredicateProducerBoundary
    true refl
    true refl
    false refl
    false refl
