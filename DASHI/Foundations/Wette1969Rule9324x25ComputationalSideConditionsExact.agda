module DASHI.Foundations.Wette1969Rule9324x25ComputationalSideConditionsExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.3.24/25 COMPUTATIONAL SIDE-CONDITION CERTIFICATES
--
-- Primary source: Eduard Wette 1969,
-- DOI: 10.1007/978-3-642-86745-3_9.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact as Rule
import DASHI.Foundations.Wette1969SchematicSubstitutionFreshnessExact as Eval
import DASHI.Foundations.Wette1969OrderedTuplePredicateSubstitutionExact as Ordered

------------------------------------------------------------------------
-- First-stage schematic side-condition bundle retained for compatibility.
------------------------------------------------------------------------

record Rule9324x25ComputationalSideConditions
    (parameters : Rule.Rule9324x25PremiseParameters) : Set where
  constructor rule9324x25ComputationalSideConditions
  field
    freshVariable : Signature.WordVariable
    freshTupleIsSchematicVariable :
      Rule.freshTupleWord parameters
        ≡ Signature.variableWordTerm freshVariable
    premise3Freshness :
      Eval.FreshVariableFor
        freshVariable
        (Rule.freshnessContextWord parameters)
    substitutionEnvironment : Eval.SubstitutionEnvironment
    premise4SchematicSubstitution :
      Eval.instantiateWordTerm
        substitutionEnvironment
        (Rule.substitutionSourceWord parameters)
      ≡ Rule.substitutionResultWord parameters

open Rule9324x25ComputationalSideConditions public

premise3FreshnessCertificate :
  {parameters : Rule.Rule9324x25PremiseParameters} →
  Rule9324x25ComputationalSideConditions parameters →
  Eval.SchematicFreshnessCertificate
premise3FreshnessCertificate {parameters} certificate =
  Eval.schematicFreshnessCertificate
    (freshVariable certificate)
    (Rule.freshnessContextWord parameters)
    (premise3Freshness certificate)

premise4SubstitutionCertificate :
  {parameters : Rule.Rule9324x25PremiseParameters} →
  Rule9324x25ComputationalSideConditions parameters →
  Eval.SchematicSubstitutionCertificate
premise4SubstitutionCertificate {parameters} certificate =
  Eval.schematicSubstitutionCertificate
    (substitutionEnvironment certificate)
    (Rule.substitutionSourceWord parameters)
    (Rule.substitutionResultWord parameters)
    (premise4SchematicSubstitution certificate)

------------------------------------------------------------------------
-- Stronger source-ordered premise-4 bundle.
--
-- The complete historical premise is now represented by its four independent II
-- arguments in Rule9324x25PremiseTemplateExact.  This older evaluator-level
-- bundle computes source -> result under the recovered stage order, but does not
-- by itself prove that its environment encodes the paired substituend and paired
-- replacement words.  That exact historical weld is owned by
-- Wette1969DependentTwoStageSubstitutionExact and the proof-carrying 8.2.8 bridge.
------------------------------------------------------------------------

record Rule9324x25OrderedComputationalSideConditions
    (parameters : Rule.Rule9324x25PremiseParameters) : Set where
  constructor rule9324x25OrderedComputationalSideConditions
  field
    orderedFreshVariable : Signature.WordVariable
    orderedFreshTupleIsSchematicVariable :
      Rule.freshTupleWord parameters
        ≡ Signature.variableWordTerm orderedFreshVariable
    orderedPremise3Freshness :
      Eval.FreshVariableFor
        orderedFreshVariable
        (Rule.freshnessContextWord parameters)

    tupleEnvironment : Eval.SubstitutionEnvironment
    recursivePredicateReplacement : Signature.WordTerm
    orderedPremise4Substitution :
      Ordered.orderedTupleThenPredicate
        tupleEnvironment
        recursivePredicateReplacement
        (Rule.substitutionSourceWord parameters)
      ≡ Rule.substitutionResultWord parameters

open Rule9324x25OrderedComputationalSideConditions public

orderedPremise3FreshnessCertificate :
  {parameters : Rule.Rule9324x25PremiseParameters} →
  Rule9324x25OrderedComputationalSideConditions parameters →
  Eval.SchematicFreshnessCertificate
orderedPremise3FreshnessCertificate {parameters} certificate =
  Eval.schematicFreshnessCertificate
    (orderedFreshVariable certificate)
    (Rule.freshnessContextWord parameters)
    (orderedPremise3Freshness certificate)

orderedPremise4SubstitutionCertificate :
  {parameters : Rule.Rule9324x25PremiseParameters} →
  Rule9324x25OrderedComputationalSideConditions parameters →
  Ordered.OrderedTuplePredicateSubstitutionCertificate
orderedPremise4SubstitutionCertificate {parameters} certificate =
  Ordered.orderedTuplePredicateSubstitutionCertificate
    (tupleEnvironment certificate)
    (recursivePredicateReplacement certificate)
    (Rule.substitutionSourceWord parameters)
    (Rule.substitutionResultWord parameters)
    (orderedPremise4Substitution certificate)

record Wette1969Rule9324x25ComputationalBoundary : Set where
  constructor wette1969Rule9324x25ComputationalBoundary
  field
    premise3FreshnessFragmentNowComputationallyCertifiable : Bool
    premise3FreshnessFragmentNowComputationallyCertifiableIsTrue :
      premise3FreshnessFragmentNowComputationallyCertifiable ≡ true

    premise4SchematicSubstitutionFragmentNowComputationallyCertifiable : Bool
    premise4SchematicSubstitutionFragmentNowComputationallyCertifiableIsTrue :
      premise4SchematicSubstitutionFragmentNowComputationallyCertifiable ≡ true

    premise4SourceOrderedTuplePredicateFragmentNowCertifiable : Bool
    premise4SourceOrderedTuplePredicateFragmentNowCertifiableIsTrue :
      premise4SourceOrderedTuplePredicateFragmentNowCertifiable ≡ true

    evaluatorCertificateAloneIdentifiesWholePairedIIArguments : Bool
    evaluatorCertificateAloneIdentifiesWholePairedIIArgumentsIsFalse :
      evaluatorCertificateAloneIdentifiesWholePairedIIArguments ≡ false

    computationalCertificateIsAlreadyHistoricalDerivabilityProof : Bool
    computationalCertificateIsAlreadyHistoricalDerivabilityProofIsFalse :
      computationalCertificateIsAlreadyHistoricalDerivabilityProof ≡ false

    orderedStructuralFragmentIsAlreadyBindingAwareHistoricalSubstitution : Bool
    orderedStructuralFragmentIsAlreadyBindingAwareHistoricalSubstitutionIsFalse :
      orderedStructuralFragmentIsAlreadyBindingAwareHistoricalSubstitution ≡ false

canonicalWette1969Rule9324x25ComputationalBoundary :
  Wette1969Rule9324x25ComputationalBoundary
canonicalWette1969Rule9324x25ComputationalBoundary =
  wette1969Rule9324x25ComputationalBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
