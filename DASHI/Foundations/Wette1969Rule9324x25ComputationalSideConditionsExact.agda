module DASHI.Foundations.Wette1969Rule9324x25ComputationalSideConditionsExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.3.24/25 COMPUTATIONAL SIDE-CONDITION CERTIFICATES
--
-- Primary source: Eduard Wette 1969,
-- DOI: 10.1007/978-3-642-86745-3_9.
--
-- This module connects the concrete schematic evaluator to the recovered
-- parameterized 9.3.24/25 premise surface.  It deliberately discharges only
-- the fragment justified by the current evaluator:
--   * premise 3 when the fresh tuple parameter is represented by one schematic
--     word variable and that variable does not occur in the freshness context;
--   * premise 4 when the recovered substitution source/result are related by
--     exact schematic instantiation under a supplied environment.
--
-- These are computational side-condition certificates, not derivability proofs
-- for Wette's historical premise formulae.  The latter remain owned by the
-- finite derivation-context / proof-carrying rule application lane.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact as Rule
import DASHI.Foundations.Wette1969SchematicSubstitutionFreshnessExact as Eval

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

record Wette1969Rule9324x25ComputationalBoundary : Set where
  constructor wette1969Rule9324x25ComputationalBoundary
  field
    premise3FreshnessFragmentNowComputationallyCertifiable : Bool
    premise3FreshnessFragmentNowComputationallyCertifiableIsTrue :
      premise3FreshnessFragmentNowComputationallyCertifiable ≡ true

    premise4SchematicSubstitutionFragmentNowComputationallyCertifiable : Bool
    premise4SchematicSubstitutionFragmentNowComputationallyCertifiableIsTrue :
      premise4SchematicSubstitutionFragmentNowComputationallyCertifiable ≡ true

    computationalCertificateIsAlreadyHistoricalDerivabilityProof : Bool
    computationalCertificateIsAlreadyHistoricalDerivabilityProofIsFalse :
      computationalCertificateIsAlreadyHistoricalDerivabilityProof ≡ false

    schematicFragmentIsAlreadyFullTuplePredicateSubstitution : Bool
    schematicFragmentIsAlreadyFullTuplePredicateSubstitutionIsFalse :
      schematicFragmentIsAlreadyFullTuplePredicateSubstitution ≡ false

canonicalWette1969Rule9324x25ComputationalBoundary :
  Wette1969Rule9324x25ComputationalBoundary
canonicalWette1969Rule9324x25ComputationalBoundary =
  wette1969Rule9324x25ComputationalBoundary
    true refl
    true refl
    false refl
    false refl
