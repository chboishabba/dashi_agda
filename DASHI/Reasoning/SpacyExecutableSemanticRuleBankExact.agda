module DASHI.Reasoning.SpacyExecutableSemanticRuleBankExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
open Candidate using
  ( Formula; Term; atom; _∧_; _∨_; _⇒_; notF; existsF; forallF
  ; DependencyWitness; DependencyShape; shape
  ; nominalSubject; directObject; passiveSubject; adjectivalModifier
  ; nominalModifier; conjunction; negation; modalAuxiliary; determiner
  ; temporalModifier
  ; CandidateSemanticFragment; candidateSemanticFragment
  ; SemanticFragmentKind; actorFragment; patientFragment; propertyFragment
  ; relationFragment; conjunctionFragment; negationFragment; modalityFragment
  ; quantifierFragment; temporalFragment; unresolvedFragment
  )

------------------------------------------------------------------------
-- EXECUTABLE SEMANTIC RULE BANK
--
-- The earlier owner established candidate semantics, but its canonical nsubj/
-- obj helpers accepted an arbitrary DependencyWitness.  This layer makes rule
-- admission proof-relevant: each executable rule requires evidence that the
-- witness really has the dependency shape licensed by that rule.
------------------------------------------------------------------------

record ShapeAdmission
    (witness : DependencyWitness)
    (required : DependencyShape) : Set where
  constructor shapeAdmission
  field
    shapeMatches : shape witness ≡ required
    ruleVersionReference : String
    parserLabelReference : String

open ShapeAdmission public

nsubjActorRule :
  (witness : DependencyWitness) →
  ShapeAdmission witness nominalSubject →
  String → String → CandidateSemanticFragment
nsubjActorRule witness admission eventName entityName =
  candidateSemanticFragment
    "rulebank-nsubj-actor"
    actorFragment
    (atom "Actor" (Candidate.eventTerm eventName ∷ Candidate.entityTerm entityName ∷ []))
    witness
    "admitted nominal subject proposes Actor(event,entity); semantic role remains candidate-only"
    (ruleVersionReference admission)
    true refl

objPatientRule :
  (witness : DependencyWitness) →
  ShapeAdmission witness directObject →
  String → String → CandidateSemanticFragment
objPatientRule witness admission eventName entityName =
  candidateSemanticFragment
    "rulebank-obj-patient"
    patientFragment
    (atom "Patient" (Candidate.eventTerm eventName ∷ Candidate.entityTerm entityName ∷ []))
    witness
    "admitted direct object proposes Patient(event,entity); semantic role remains candidate-only"
    (ruleVersionReference admission)
    true refl

passiveSubjectPatientRule :
  (witness : DependencyWitness) →
  ShapeAdmission witness passiveSubject →
  String → String → CandidateSemanticFragment
passiveSubjectPatientRule witness admission eventName entityName =
  candidateSemanticFragment
    "rulebank-passive-subject-patient"
    patientFragment
    (atom "Patient" (Candidate.eventTerm eventName ∷ Candidate.entityTerm entityName ∷ []))
    witness
    "passive nominal subject proposes patient/event role, not actor role"
    (ruleVersionReference admission)
    true refl

adjectivalPropertyRule :
  (witness : DependencyWitness) →
  ShapeAdmission witness adjectivalModifier →
  String → String → CandidateSemanticFragment
adjectivalPropertyRule witness admission propertyName entityName =
  candidateSemanticFragment
    "rulebank-amod-property"
    propertyFragment
    (atom propertyName (Candidate.entityTerm entityName ∷ []))
    witness
    "adjectival modifier proposes a property of the modified entity"
    (ruleVersionReference admission)
    true refl

nominalRelationRule :
  (witness : DependencyWitness) →
  ShapeAdmission witness nominalModifier →
  String → String → String → CandidateSemanticFragment
nominalRelationRule witness admission relationName left right =
  candidateSemanticFragment
    "rulebank-nmod-relation"
    relationFragment
    (atom relationName (Candidate.entityTerm left ∷ Candidate.entityTerm right ∷ []))
    witness
    "nominal modifier proposes a relation; attachment interpretation remains reviewable"
    (ruleVersionReference admission)
    true refl

negationScopeRule :
  (witness : DependencyWitness) →
  ShapeAdmission witness negation →
  Formula → CandidateSemanticFragment
negationScopeRule witness admission body =
  candidateSemanticFragment
    "rulebank-negation"
    negationFragment
    (notF body)
    witness
    "dependency negation proposes logical negation over the nominated body; scope is not silently fixed"
    (ruleVersionReference admission)
    true refl

conjunctionRule :
  (witness : DependencyWitness) →
  ShapeAdmission witness conjunction →
  Formula → Formula → CandidateSemanticFragment
conjunctionRule witness admission left right =
  candidateSemanticFragment
    "rulebank-conjunction"
    conjunctionFragment
    (left ∧ right)
    witness
    "conj dependency proposes conjunction of two resolved semantic fragments"
    (ruleVersionReference admission)
    true refl

------------------------------------------------------------------------
-- Determiner/quantifier semantics require both syntactic admission and a
-- lexical reading receipt.  A bare det edge does not decide forall vs exists.
------------------------------------------------------------------------

data DeterminerReading : Set where
  universalDeterminer
  existentialDeterminer
  unresolvedDeterminer
  : DeterminerReading

record DeterminerResolution
    (witness : DependencyWitness)
    (reading : DeterminerReading) : Set where
  constructor determinerResolution
  field
    determinerShape : ShapeAdmission witness determiner
    lexicalFormReference : String
    scopeReference : String
    resolverReference : String

open DeterminerResolution public

universalDeterminerRule :
  (witness : DependencyWitness) →
  DeterminerResolution witness universalDeterminer →
  String → String → Formula → CandidateSemanticFragment
universalDeterminerRule witness resolution variable domain body =
  candidateSemanticFragment
    "rulebank-det-universal"
    quantifierFragment
    (forallF variable domain body)
    witness
    "resolved determiner proposes universal quantification over the nominated scope"
    (resolverReference resolution)
    true refl

existentialDeterminerRule :
  (witness : DependencyWitness) →
  DeterminerResolution witness existentialDeterminer →
  String → String → Formula → CandidateSemanticFragment
existentialDeterminerRule witness resolution variable domain body =
  candidateSemanticFragment
    "rulebank-det-existential"
    quantifierFragment
    (existsF variable domain body)
    witness
    "resolved determiner proposes existential quantification over the nominated scope"
    (resolverReference resolution)
    true refl

------------------------------------------------------------------------
-- Modal and temporal dependencies are retained as explicit qualification
-- predicates in first-order candidate semantics.  They are not given modal or
-- temporal proof rules merely because spaCy observed an auxiliary/modifier.
------------------------------------------------------------------------

modalQualificationRule :
  (witness : DependencyWitness) →
  ShapeAdmission witness modalAuxiliary →
  String → String → CandidateSemanticFragment
modalQualificationRule witness admission modalReading eventName =
  candidateSemanticFragment
    "rulebank-modal-qualification"
    modalityFragment
    (atom "ModalQualification"
      (Candidate.eventTerm eventName ∷ Candidate.literalTerm modalReading ∷ []))
    witness
    "modal auxiliary proposes a modality qualification; force/scope remains an evidential interpretation obligation"
    (ruleVersionReference admission)
    true refl

temporalQualificationRule :
  (witness : DependencyWitness) →
  ShapeAdmission witness temporalModifier →
  String → String → CandidateSemanticFragment
temporalQualificationRule witness admission eventName temporalReading =
  candidateSemanticFragment
    "rulebank-temporal-qualification"
    temporalFragment
    (atom "TemporalQualification"
      (Candidate.eventTerm eventName ∷ Candidate.literalTerm temporalReading ∷ []))
    witness
    "temporal modifier proposes an event/time relation without promoting causal direction"
    (ruleVersionReference admission)
    true refl

------------------------------------------------------------------------
-- Composite constructions. Relative clauses and conditionals generally need
-- several dependency observations, so they are admitted over already-reviewed
-- candidate formulae plus an explicit attachment/marker receipt rather than by
-- pretending one dependency label uniquely determines their scope.
------------------------------------------------------------------------

record RelativeClauseComposition : Set where
  constructor relativeClauseComposition
  field
    headFormula : Formula
    clauseFormula : Formula
    attachmentWitnesses : List DependencyWitness
    attachmentReference : String
    antecedentIdentityReference : String

open RelativeClauseComposition public

relativeClauseRule : RelativeClauseComposition → Formula
relativeClauseRule composition =
  headFormula composition ∧ clauseFormula composition

record ConditionalComposition : Set where
  constructor conditionalComposition
  field
    antecedent : Formula
    consequent : Formula
    markerWitnesses : List DependencyWitness
    conditionalMarkerReference : String
    scopeReference : String

open ConditionalComposition public

conditionalRule : ConditionalComposition → Formula
conditionalRule composition =
  antecedent composition ⇒ consequent composition

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

record ExecutableSemanticRuleBoundary : Set where
  constructor executableSemanticRuleBoundary
  field
    arbitraryDependencyMayEnterNsubjRule : Bool
    arbitraryDependencyMayEnterNsubjRuleIsFalse :
      arbitraryDependencyMayEnterNsubjRule ≡ false
    determinerEdgeUniquelyChoosesQuantifier : Bool
    determinerEdgeUniquelyChoosesQuantifierIsFalse :
      determinerEdgeUniquelyChoosesQuantifier ≡ false
    passiveSubjectDefaultsToActor : Bool
    passiveSubjectDefaultsToActorIsFalse : passiveSubjectDefaultsToActor ≡ false
    modalAuxiliaryCreatesModalTheorem : Bool
    modalAuxiliaryCreatesModalTheoremIsFalse : modalAuxiliaryCreatesModalTheorem ≡ false
    relativeClauseMayRequireCompositeEvidence : Bool
    relativeClauseMayRequireCompositeEvidenceIsTrue :
      relativeClauseMayRequireCompositeEvidence ≡ true
    conditionalMayRequireCompositeEvidence : Bool
    conditionalMayRequireCompositeEvidenceIsTrue :
      conditionalMayRequireCompositeEvidence ≡ true

canonicalExecutableSemanticRuleBoundary : ExecutableSemanticRuleBoundary
canonicalExecutableSemanticRuleBoundary =
  executableSemanticRuleBoundary
    false refl false refl false refl false refl true refl true refl
