module DASHI.Foundations.Wette1969SchematicSubstitutionFreshnessExact where

------------------------------------------------------------------------
-- WETTE 1969 SCHEMATIC SUBSTITUTION / FRESHNESS EVALUATOR
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- This module attacks the computational side of the recovered critical rules
-- conservatively. Wette's rule schemata use nineteen word variables, and the
-- historical syntax owner already distinguishes WordTerm from concrete Word.
-- We implement exact structural instantiation of those schematic word variables
-- and a proof-relevant occurrence/freshness judgement on WordTerm.
--
-- This is NOT yet the full object-language tuple/predicate substitution relation
-- described by Wette's four-place substitution relator on p.148. In particular
-- it does not manufacture capture-avoidance for bound predicate/variable
-- operations. It provides a concrete evaluator for schematic substitution and
-- concrete certificates for the freshness side-condition fragment.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature

WordTerm = Signature.WordTerm
WordVariable = Signature.WordVariable

SubstitutionEnvironment : Set
SubstitutionEnvironment = WordVariable → WordTerm

instantiateWordTerm : SubstitutionEnvironment → WordTerm → WordTerm
instantiateWordTerm environment (Signature.variableWordTerm variable) =
  environment variable
instantiateWordTerm environment (Signature.constantWordTerm constant) =
  Signature.constantWordTerm constant
instantiateWordTerm environment
  (Signature.unaryWordTerm functor arity term) =
  Signature.unaryWordTerm functor arity
    (instantiateWordTerm environment term)
instantiateWordTerm environment
  (Signature.binaryWordTerm functor arity left right) =
  Signature.binaryWordTerm functor arity
    (instantiateWordTerm environment left)
    (instantiateWordTerm environment right)

------------------------------------------------------------------------
-- Proof-relevant schematic-variable occurrence and freshness.
------------------------------------------------------------------------

data OccursVariable (variable : WordVariable) : WordTerm → Set where
  occursHere : OccursVariable variable (Signature.variableWordTerm variable)
  occursUnary :
    ∀ {functor arity term} →
    OccursVariable variable term →
    OccursVariable variable (Signature.unaryWordTerm functor arity term)
  occursBinaryLeft :
    ∀ {functor arity left right} →
    OccursVariable variable left →
    OccursVariable variable
      (Signature.binaryWordTerm functor arity left right)
  occursBinaryRight :
    ∀ {functor arity left right} →
    OccursVariable variable right →
    OccursVariable variable
      (Signature.binaryWordTerm functor arity left right)

FreshVariableFor : WordVariable → WordTerm → Set
FreshVariableFor variable term = ¬ OccursVariable variable term

freshConstant :
  (variable : WordVariable) →
  (constant : Signature.HistoricalConstant) →
  FreshVariableFor variable (Signature.constantWordTerm constant)
freshConstant variable constant ()

freshUnary :
  ∀ {variable functor arity term} →
  FreshVariableFor variable term →
  FreshVariableFor variable (Signature.unaryWordTerm functor arity term)
freshUnary freshness (occursUnary occurrence) = freshness occurrence

freshBinary :
  ∀ {variable functor arity left right} →
  FreshVariableFor variable left →
  FreshVariableFor variable right →
  FreshVariableFor variable
    (Signature.binaryWordTerm functor arity left right)
freshBinary leftFresh rightFresh (occursBinaryLeft occurrence) =
  leftFresh occurrence
freshBinary leftFresh rightFresh (occursBinaryRight occurrence) =
  rightFresh occurrence

------------------------------------------------------------------------
-- Extensional evaluator theorem.
------------------------------------------------------------------------

environmentsAgreeOn :
  SubstitutionEnvironment →
  SubstitutionEnvironment →
  WordTerm →
  Set
environmentsAgreeOn left right term =
  (variable : WordVariable) →
  OccursVariable variable term →
  left variable ≡ right variable

instantiateCongOnOccurrences :
  (left right : SubstitutionEnvironment) →
  (term : WordTerm) →
  environmentsAgreeOn left right term →
  instantiateWordTerm left term ≡ instantiateWordTerm right term
instantiateCongOnOccurrences left right
  (Signature.variableWordTerm variable) agreement =
  agreement variable occursHere
instantiateCongOnOccurrences left right
  (Signature.constantWordTerm constant) agreement = refl
instantiateCongOnOccurrences left right
  (Signature.unaryWordTerm functor arity term) agreement =
  cong
    (Signature.unaryWordTerm functor arity)
    (instantiateCongOnOccurrences left right term
      (λ variable occurrence → agreement variable (occursUnary occurrence)))
instantiateCongOnOccurrences left right
  (Signature.binaryWordTerm functor arity first second) agreement =
  cong₂
    (Signature.binaryWordTerm functor arity)
    (instantiateCongOnOccurrences left right first
      (λ variable occurrence → agreement variable (occursBinaryLeft occurrence)))
    (instantiateCongOnOccurrences left right second
      (λ variable occurrence → agreement variable (occursBinaryRight occurrence)))
  where
    cong₂ :
      ∀ {A B C : Set} {x x' : A} {y y' : B} →
      (f : A → B → C) →
      x ≡ x' → y ≡ y' →
      f x y ≡ f x' y'
    cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Concrete certificates exposed to critical-rule consumers.
------------------------------------------------------------------------

record SchematicFreshnessCertificate : Set where
  constructor schematicFreshnessCertificate
  field
    variable : WordVariable
    term : WordTerm
    fresh : FreshVariableFor variable term

open SchematicFreshnessCertificate public

record SchematicSubstitutionCertificate : Set where
  constructor schematicSubstitutionCertificate
  field
    environment : SubstitutionEnvironment
    source : WordTerm
    result : WordTerm
    evaluates : instantiateWordTerm environment source ≡ result

open SchematicSubstitutionCertificate public

canonicalSubstitutionCertificate :
  (environment : SubstitutionEnvironment) →
  (source : WordTerm) →
  SchematicSubstitutionCertificate
canonicalSubstitutionCertificate environment source =
  schematicSubstitutionCertificate
    environment
    source
    (instantiateWordTerm environment source)
    refl

record Wette1969SchematicSubstitutionFreshnessBoundary : Set where
  constructor wette1969SchematicSubstitutionFreshnessBoundary
  field
    schematicWordVariableSubstitutionNowExecutable : Bool
    schematicWordVariableSubstitutionNowExecutableIsTrue :
      schematicWordVariableSubstitutionNowExecutable ≡ true

    freshnessCertificatesNowProofRelevant : Bool
    freshnessCertificatesNowProofRelevantIsTrue :
      freshnessCertificatesNowProofRelevant ≡ true

    substitutionExactnessDependsOnlyOnOccurringVariables : Bool
    substitutionExactnessDependsOnlyOnOccurringVariablesIsTrue :
      substitutionExactnessDependsOnlyOnOccurringVariables ≡ true

    evaluatorAlreadyImplementsFullObjectLanguageTupleSubstitution : Bool
    evaluatorAlreadyImplementsFullObjectLanguageTupleSubstitutionIsFalse :
      evaluatorAlreadyImplementsFullObjectLanguageTupleSubstitution ≡ false

    evaluatorAlreadyProvesCaptureAvoidanceForPredicateBinders : Bool
    evaluatorAlreadyProvesCaptureAvoidanceForPredicateBindersIsFalse :
      evaluatorAlreadyProvesCaptureAvoidanceForPredicateBinders ≡ false

canonicalWette1969SchematicSubstitutionFreshnessBoundary :
  Wette1969SchematicSubstitutionFreshnessBoundary
canonicalWette1969SchematicSubstitutionFreshnessBoundary =
  wette1969SchematicSubstitutionFreshnessBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
