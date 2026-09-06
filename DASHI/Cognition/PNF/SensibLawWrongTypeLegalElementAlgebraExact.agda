module DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact where

------------------------------------------------------------------------
-- WRONGTYPE -> LEGAL ELEMENT -> REQUIREMENT -> RULE GRAPH
--
-- The schema already owned wrongElement / wrongElementRequirement / normAtom /
-- provision. This module promotes that latent topology into proof-relevant
-- theorem objects without replacing the existing WrongType owner.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Existing

------------------------------------------------------------------------
-- Element kinds are reusable across WrongTypes; the proposition remains indexed
-- to the exact WrongType/system/event relation through its atom.
------------------------------------------------------------------------

data LegalElementKind : Set where
  dutyElement
  breachElement
  causationElement
  damageElement
  mentalStateElement
  statutoryElement
  jurisdictionElement
  standingElement
  limitationElement
  defenceElement
  remedyElement
  otherElement
  : LegalElementKind

record LegalElement (wrong : Ontology.WrongType) : Set where
  constructor legal-element
  field
    elementId : Ontology.StableId
    kind : LegalElementKind
    proposition : Algebra.LegalProposition
    sameSystem :
      Algebra.LegalProposition.legalSystem proposition
      ≡ Ontology.WrongType.definingSystem wrong

open LegalElement public

record ElementRequirement
  {wrong : Ontology.WrongType}
  (element : LegalElement wrong)
  : Set where
  constructor element-requirement
  field
    requirementId : Ontology.StableId
    requiredProposition : Algebra.LegalProposition
    authorityRule : Algebra.LegalRule
    ruleConcludesElementOrRequirement : Set

open ElementRequirement public

record WrongTypeRuleBundle (wrong : Ontology.WrongType) : Set where
  constructor wrong-type-rule-bundle
  field
    elements : List (LegalElement wrong)
    ruleGraph : Algebra.LegalGraph
    sourceIdsPreserved : Set
    protectedInterestsPreserved : Set
    actorConstraintsPreserved : Set
    relationshipConstraintsPreserved : Set
    harmClassesPreserved : Set
    remediesPreserved : Set

open WrongTypeRuleBundle public

------------------------------------------------------------------------
-- Element proof is a derivation in the universal graph, not an opaque status.
------------------------------------------------------------------------

record ElementDerivation
  {wrong : Ontology.WrongType}
  (bundle : WrongTypeRuleBundle wrong)
  (facts : Algebra.FactSet)
  (element : LegalElement wrong)
  : Set where
  constructor element-derivation
  field
    proof : Algebra.Reachable
      (WrongTypeRuleBundle.ruleGraph bundle)
      facts
      (LegalElement.proposition element)

open ElementDerivation public

------------------------------------------------------------------------
-- Bridge to the existing WrongElementEvaluation surface.
--
-- This compiler intentionally forgets proof structure only at the old API
-- boundary; the source derivation remains separately available.
------------------------------------------------------------------------

record ExistingElementEvaluationBridge
  {wrong : Ontology.WrongType}
  {bundle : WrongTypeRuleBundle wrong}
  {facts : Algebra.FactSet}
  (element : LegalElement wrong)
  : Set where
  constructor existing-element-evaluation-bridge
  field
    derivation : ElementDerivation bundle facts element
    legacyEvaluation : Existing.WrongElementEvaluation
    sameWrongTypeId :
      Existing.WrongElementEvaluation.wrongTypeReference legacyEvaluation
      ≡ Ontology.WrongType.wrongTypeId wrong
    legacyReferenceNamesElement : String

open ExistingElementEvaluationBridge public

------------------------------------------------------------------------
-- Downstream violation should ultimately consume a set of element derivations.
------------------------------------------------------------------------

record ProofRelevantViolationBasis
  (wrong : Ontology.WrongType)
  (bundle : WrongTypeRuleBundle wrong)
  (facts : Algebra.FactSet)
  : Set where
  constructor proof-relevant-violation-basis
  field
    provedElements :
      ∀ {element} →
      Algebra._∈_ element (WrongTypeRuleBundle.elements bundle) →
      ElementDerivation bundle facts element
    legacyViolationReceipt : Existing.ViolationReceipt
    sameWrongType :
      Ontology.WrongType.wrongTypeId wrong
      ≡ Ontology.WrongType.wrongTypeId
          (Existing.wrongType
            (Existing.applicabilityReceipt legacyViolationReceipt))

open ProofRelevantViolationBasis public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ElementStringReferenceIsElementProof : Set where
data WrongTypeIdAloneDeterminesAllElements : Set where
data ElementDerivationAutomaticallyCreatesLiability : Set where

stringReferenceDoesNotProveElement : ElementStringReferenceIsElementProof → ⊥
stringReferenceDoesNotProveElement ()

wrongTypeIdDoesNotGenerateElements : WrongTypeIdAloneDeterminesAllElements → ⊥
wrongTypeIdDoesNotGenerateElements ()

elementProofDoesNotAutoCreateLiability : ElementDerivationAutomaticallyCreatesLiability → ⊥
elementProofDoesNotAutoCreateLiability ()
