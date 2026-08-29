module DASHI.Foundations.Wette1969Rule915PredicateProducerExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: PREDICATE-SCHEMA PRODUCER
--
-- Eduard Wette, 1969, DOI 10.1007/978-3-642-86745-3_9.
--
-- Printed p.145 gives 27 premises. Section 1.61 says the first seven are the
-- skeletal/formation layer and the remaining twenty are caused by L. Those
-- first seven are source-readable and now constructed literally here:
--
--   1. 2 V W       W doubles the arity word V
--   2. n V W2      W2 is a V-place predicate mark
--   3. u_x V V2    V2 is a V-tuple of distinct variables
--   4. p V V1      V1 is a V-place predicate schema
--   5. p W W1      W1 is a W-place predicate schema
--   6. _A U        p.193 modified assertion-schema condition
--   7. A U1        U1 is an assertion schema
--
-- Premises 8--27 remain slot-indexed transcription obligations. This is a
-- stronger boundary than allowing all 27 formulae to float arbitrarily while
-- still refusing to fabricate the OCR-sensitive L-generated block.
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

------------------------------------------------------------------------
-- Exact first-seven constructor surface.
------------------------------------------------------------------------

record Rule915FirstSevenParameters : Set where
  constructor rule915FirstSevenParameters
  field
    arityWord : WordTerm
    doubledArityWord : WordTerm
    predicateMarkWord : WordTerm
    variableTupleWord : WordTerm
    predicateSchemaWord : WordTerm
    doubledPredicateSchemaWord : WordTerm
    definiensSchemaWord : WordTerm
    definitionPrerequisiteWord : WordTerm

open Rule915FirstSevenParameters public

premise915-01 : Rule915FirstSevenParameters → Formula
premise915-01 parameters =
  Judgment.duplicates
    (arityWord parameters)
    (doubledArityWord parameters)

premise915-02 : Rule915FirstSevenParameters → Formula
premise915-02 parameters =
  Judgment.predicateMarkArity
    (arityWord parameters)
    (predicateMarkWord parameters)

premise915-03 : Rule915FirstSevenParameters → Formula
premise915-03 parameters =
  Judgment.distinctVariableTuple
    (arityWord parameters)
    (variableTupleWord parameters)

premise915-04 : Rule915FirstSevenParameters → Formula
premise915-04 parameters =
  Judgment.predicateSchema
    (arityWord parameters)
    (predicateSchemaWord parameters)

premise915-05 : Rule915FirstSevenParameters → Formula
premise915-05 parameters =
  Judgment.predicateSchema
    (doubledArityWord parameters)
    (doubledPredicateSchemaWord parameters)

premise915-06 : Rule915FirstSevenParameters → Formula
premise915-06 parameters =
  Judgment.assertionSchemaNoPredicateQuantification
    (definiensSchemaWord parameters)

premise915-07 : Rule915FirstSevenParameters → Formula
premise915-07 parameters =
  Judgment.assertionSchema
    (definitionPrerequisiteWord parameters)

-- Supply only the still-unrecovered L-generated block. Values returned for the
-- first seven slots by `laterPremise` are definitionally ignored.
exactFirstSevenTranscription :
  Rule915FirstSevenParameters →
  (laterPremise : Critical.Premise915 → Formula) →
  Rule915PremiseTranscription
exactFirstSevenTranscription parameters laterPremise =
  rule915PremiseTranscription exact
  where
    exact : Critical.Premise915 → Formula
    exact Critical.p01 = premise915-01 parameters
    exact Critical.p02 = premise915-02 parameters
    exact Critical.p03 = premise915-03 parameters
    exact Critical.p04 = premise915-04 parameters
    exact Critical.p05 = premise915-05 parameters
    exact Critical.p06 = premise915-06 parameters
    exact Critical.p07 = premise915-07 parameters
    exact Critical.p08 = laterPremise Critical.p08
    exact Critical.p09 = laterPremise Critical.p09
    exact Critical.p10 = laterPremise Critical.p10
    exact Critical.p11 = laterPremise Critical.p11
    exact Critical.p12 = laterPremise Critical.p12
    exact Critical.p13 = laterPremise Critical.p13
    exact Critical.p14 = laterPremise Critical.p14
    exact Critical.p15 = laterPremise Critical.p15
    exact Critical.p16 = laterPremise Critical.p16
    exact Critical.p17 = laterPremise Critical.p17
    exact Critical.p18 = laterPremise Critical.p18
    exact Critical.p19 = laterPremise Critical.p19
    exact Critical.p20 = laterPremise Critical.p20
    exact Critical.p21 = laterPremise Critical.p21
    exact Critical.p22 = laterPremise Critical.p22
    exact Critical.p23 = laterPremise Critical.p23
    exact Critical.p24 = laterPremise Critical.p24
    exact Critical.p25 = laterPremise Critical.p25
    exact Critical.p26 = laterPremise Critical.p26
    exact Critical.p27 = laterPremise Critical.p27

modifiedPremise6UsesNoPredicateQuantificationRelator :
  (parameters : Rule915FirstSevenParameters) →
  Signature.relator (premise915-06 parameters)
    ≡ Signature.assertionSchemaNoPredicateQuantificationRelator
modifiedPremise6UsesNoPredicateQuantificationRelator parameters = refl

firstSevenAreFixedBySource :
  (parameters : Rule915FirstSevenParameters) →
  (laterPremise : Critical.Premise915 → Formula) →
  premiseAt (exactFirstSevenTranscription parameters laterPremise) Critical.p03
    ≡ Judgment.distinctVariableTuple
        (arityWord parameters)
        (variableTupleWord parameters)
firstSevenAreFixedBySource parameters laterPremise = refl

------------------------------------------------------------------------
-- Full 27-slot rule carrier.
------------------------------------------------------------------------

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
  WordTerm → WordTerm → RuleBody.HistoricalRuleBody
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
    Finite.finiteHistoricalContextSystem context
    (rule9-1-5 transcription arity recursivePredicate) →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule915 context transcription arity recursivePredicate evidence =
  PCRA.selectedRuleApplication
    (rule9-1-5 transcription arity recursivePredicate)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context
      (rule9-1-5 transcription arity recursivePredicate)
      evidence)

predicateSchemaAvailableAfter915 :
  (context : Context) →
  (transcription : Rule915PremiseTranscription) →
  (arity recursivePredicate : WordTerm) →
  (evidence :
    Historical.PremisesHold
      Finite.finiteHistoricalContextSystem context
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
    firstSevenPremiseBodiesNowLiteralSourceConstructors : Bool
    firstSevenPremiseBodiesNowLiteralSourceConstructorsIsTrue :
      firstSevenPremiseBodiesNowLiteralSourceConstructors ≡ true
    modifiedPremise6UsesP193NoPredicateQuantificationCondition : Bool
    modifiedPremise6UsesP193NoPredicateQuantificationConditionIsTrue :
      modifiedPremise6UsesP193NoPredicateQuantificationCondition ≡ true
    remainingTwentyLPremisesStillExplicitTranscriptionObligations : Bool
    remainingTwentyLPremisesStillExplicitTranscriptionObligationsIsTrue :
      remainingTwentyLPremisesStillExplicitTranscriptionObligations ≡ true
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
    true refl true refl true refl true refl true refl false refl false refl
