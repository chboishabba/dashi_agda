module DASHI.Cognition.PNF.SensibLawSourceConditionedApplicabilityViolationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact as Meet
import DASHI.Cognition.PNF.SensibLawViolationPrerequisiteMeetExact as Violation
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule

------------------------------------------------------------------------
-- SOURCE-CONDITIONED APPLICABILITY
--
-- ApplicabilityPrerequisiteMeet remains the canonical semantic/same-object
-- prerequisite meet.  This owner adds the legal-rule layer: the source-realised
-- rule itself determines its premises, exceptions and defeaters, while typed
-- jurisdiction and temporal predicates are separately derived.
------------------------------------------------------------------------

record SourceConditionedApplicability
    {state : DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact.SemanticCommitmentState}
    (graph : Algebra.LegalGraph)
    (facts : Algebra.FactSet)
    (Enabled : Algebra.LegalRule → Set)
    (r : Algebra.LegalRule) : Set₁ where
  constructor source-conditioned-applicability
  field
    ruleInGraph : Algebra._∈_ r (Algebra.rules graph)
    ruleEnabled : Enabled r
    sourceRealisation : SourceRule.SourceRealisedLegalRule r
    semanticMeet : Meet.ApplicabilityMeetInput state

    premisesPaid :
      Algebra.All (Algebra.Derivation graph facts Enabled) (Algebra.premises r)
    exceptionsInactive :
      Algebra.All
        (λ e → Algebra.Derivation graph facts Enabled e → ⊥)
        (Algebra.exceptions r)
    defeatersInactive :
      Algebra.All
        (λ d → Algebra.Derivation graph facts Enabled d → ⊥)
        (Algebra.defeaters r)

    jurisdictionPaid :
      Algebra.Derivation graph facts Enabled
        (SourceRule.jurisdictionPredicate sourceRealisation)
    temporalPaid :
      Algebra.Derivation graph facts Enabled
        (SourceRule.temporalPredicate sourceRealisation)

    wrongTypeSystemMatchesRule :
      Ontology.WrongType.definingSystem (Meet.wrongType semanticMeet)
      ≡ SourceRule.ruleSystem sourceRealisation

    applicabilityReference : String

open SourceConditionedApplicability public

sourceConditionedRuleConclusion :
  ∀ {state graph facts Enabled r} →
  SourceConditionedApplicability {state} graph facts Enabled r →
  Algebra.Derivation graph facts Enabled (Algebra.conclusion r)
sourceConditionedRuleConclusion applicable =
  Algebra.byRule
    (ruleInGraph applicable)
    (ruleEnabled applicable)
    (premisesPaid applicable)
    (exceptionsInactive applicable)
    (defeatersInactive applicable)

semanticApplicabilityProjection :
  ∀ {state graph facts Enabled r} →
  SourceConditionedApplicability {state} graph facts Enabled r →
  Legal.WrongTypeApplicabilityReceipt
semanticApplicabilityProjection applicable =
  Meet.compileApplicabilityMeet (semanticMeet applicable)

------------------------------------------------------------------------
-- SOURCE-REALISED ELEMENT REQUIREMENTS
------------------------------------------------------------------------

record SourceRealisedElementRequirement
    {wrong : Ontology.WrongType}
    (element : Elements.LegalElement wrong) : Set₁ where
  constructor source-realised-element-requirement
  field
    requirement : Elements.ElementRequirement element
    sourceRealisedAuthorityRule :
      SourceRule.SourceRealisedLegalRule (Elements.authorityRule requirement)
    requirementPropositionMatchesElementSystem :
      Algebra.legalSystem (Elements.requiredProposition requirement)
      ≡ Ontology.WrongType.definingSystem wrong
    requirementReference : String

open SourceRealisedElementRequirement public

------------------------------------------------------------------------
-- SOURCE-CONDITIONED VIOLATION
--
-- The exact WrongTypeRuleBundle is authoritative for which LegalElements are
-- required.  Every element in that bundle needs both a source-realised element
-- requirement and an ElementDerivation on the same fact fibre.  This is stricter
-- than the legacy ViolationMeetInput, whose evaluations need only share a
-- WrongType id.
------------------------------------------------------------------------

record SourceConditionedViolation
    {state : DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact.SemanticCommitmentState}
    (wrong : Ontology.WrongType)
    (bundle : Elements.WrongTypeRuleBundle wrong)
    (facts : Algebra.FactSet) : Set₁ where
  constructor source-conditioned-violation
  field
    applicabilityRule : Algebra.LegalRule
    applicability :
      SourceConditionedApplicability
        (Elements.ruleGraph bundle)
        facts
        (λ _ → ⊤)
        applicabilityRule

    applicabilityWrongTypeMatches :
      Meet.wrongType (semanticMeet applicability) ≡ wrong

    sourceRealisedRequirements :
      ∀ {element} →
      Algebra._∈_ element (Elements.elements bundle) →
      SourceRealisedElementRequirement element

    elementDerivations :
      ∀ {element} →
      Algebra._∈_ element (Elements.elements bundle) →
      Elements.ElementDerivation bundle facts element

    legacyViolationMeet : Violation.ViolationMeetInput state
    legacyViolationWrongTypeMatches :
      Legal.wrongType
        (Violation.receipt
          (Violation.applicability
            (Violation.prerequisites legacyViolationMeet)))
      ≡ wrong

    sourceDefinedNegativeBranchesChecked : Bool
    sourceDefinedNegativeBranchesCheckedIsTrue :
      sourceDefinedNegativeBranchesChecked ≡ true

    violationReference : String

open SourceConditionedViolation public

legacyViolationProjection :
  ∀ {state wrong bundle facts} →
  SourceConditionedViolation {state} wrong bundle facts →
  Legal.ViolationReceipt
legacyViolationProjection sourceViolation =
  Violation.compileViolationMeet (legacyViolationMeet sourceViolation)

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data SemanticMeetAloneProvesLegalApplicability : Set where
data SameWrongTypeEvaluationsDefineRequiredElements : Set where
data AllElementsProvedIgnoresExceptionsDefences : Set where
data SourceRealisedWrongTypeAutomaticallyViolated : Set where
\data SourceMetadataAroundRuleEqualsSourceRealisedRule : Set where

semanticMeetDoesNotAloneProveLegalApplicability :
  SemanticMeetAloneProvesLegalApplicability → ⊥
semanticMeetDoesNotAloneProveLegalApplicability ()

sameWrongTypeEvaluationsDoNotDefineRequiredElements :
  SameWrongTypeEvaluationsDefineRequiredElements → ⊥
sameWrongTypeEvaluationsDoNotDefineRequiredElements ()

allElementsDoNotEraseExceptionsDefences :
  AllElementsProvedIgnoresExceptionsDefences → ⊥
allElementsDoNotEraseExceptionsDefences ()

sourceRealisedWrongTypeDoesNotAutoViolate :
  SourceRealisedWrongTypeAutomaticallyViolated → ⊥
sourceRealisedWrongTypeDoesNotAutoViolate ()

sourceMetadataIsNotRuleRealisation :
  SourceMetadataAroundRuleEqualsSourceRealisedRule → ⊥
sourceMetadataIsNotRuleRealisation ()

record SourceConditionedApplicabilityViolationBoundary : Set where
  constructor source-conditioned-applicability-violation-boundary
  field
    semanticMeetRetained : Bool
    governingRuleMustBeSourceRealised : Bool
    premisesMustBeDerived : Bool
    exceptionsMustBeInactive : Bool
    defeatersMustBeInactive : Bool
    jurisdictionMustBeTypedAndDerived : Bool
    temporalScopeMustBeTypedAndDerived : Bool
    wrongTypeBundleDefinesElementUniverse : Bool
    everyRequiredElementNeedsSourceRealisation : Bool
    everyRequiredElementNeedsDerivation : Bool
    legacyAdaptersRemainProjectionOnly : Bool

canonicalSourceConditionedApplicabilityViolationBoundary :
  SourceConditionedApplicabilityViolationBoundary
canonicalSourceConditionedApplicabilityViolationBoundary =
  source-conditioned-applicability-violation-boundary
    true true true true true true true true true true true
