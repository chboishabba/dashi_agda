module DASHI.Cognition.PNF.SensibLawSourceConditionedApplicabilityViolationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact as Meet
import DASHI.Cognition.PNF.SensibLawViolationPrerequisiteMeetExact as Violation
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawSourceConditionedAtomicLegalImplicationExact as AtomicImplication

record SourceConditionedApplicability
    {state : Status.SemanticCommitmentState}
    (graph : Algebra.LegalGraph)
    (facts : Algebra.FactSet)
    (Enabled : Algebra.LegalRule → Set)
    (r : Algebra.LegalRule) : Set₁ where
  constructor source-conditioned-applicability
  field
    atomicRuleApplication :
      AtomicImplication.SourceConditionedAtomicLegalImplication graph facts Enabled r
    atomicRuleDerivationReceipt :
      AtomicImplication.AtomicImplicationDerivationReceipt atomicRuleApplication
    semanticMeet : Meet.ApplicabilityMeetInput state
    wrongTypeSystemMatchesRule :
      Ontology.WrongType.definingSystem (Meet.wrongType semanticMeet)
      ≡ SourceRule.ruleSystem (AtomicImplication.sourceRealisation atomicRuleApplication)
    applicabilityReference : String

open SourceConditionedApplicability public

sourceConditionedRuleConclusion :
  ∀ {state graph facts Enabled r} →
  SourceConditionedApplicability {state} graph facts Enabled r →
  Algebra.Derivation graph facts Enabled (Algebra.conclusion r)
sourceConditionedRuleConclusion applicable =
  AtomicImplication.compileAtomicLegalImplication
    (atomicRuleApplication applicable)
    (atomicRuleDerivationReceipt applicable)

semanticApplicabilityProjection :
  ∀ {state graph facts Enabled r} →
  SourceConditionedApplicability {state} graph facts Enabled r →
  Legal.WrongTypeApplicabilityReceipt
semanticApplicabilityProjection applicable =
  Meet.compileApplicabilityMeet (semanticMeet applicable)

record SourceConditionedElementRequirement
    {wrong : Ontology.WrongType}
    (bundle : Elements.WrongTypeRuleBundle wrong)
    (facts : Algebra.FactSet)
    (element : Elements.LegalElement wrong) : Set₁ where
  constructor source-conditioned-element-requirement
  field
    requirement : Elements.ElementRequirement element
    authorityRuleApplication :
      AtomicImplication.SourceConditionedAtomicLegalImplication
        (Elements.ruleGraph bundle) facts (λ _ → ⊤)
        (Elements.authorityRule requirement)
    authorityRuleDerivationReceipt :
      AtomicImplication.AtomicImplicationDerivationReceipt authorityRuleApplication
    authorityRuleConclusionIsRequiredProposition :
      Algebra.conclusion (Elements.authorityRule requirement)
      ≡ Elements.requiredProposition requirement
    requiredPropositionIsExactElement :
      Elements.requiredProposition requirement ≡ Elements.proposition element
    requirementReference : String

open SourceConditionedElementRequirement public

sourceConditionedElementConclusion :
  ∀ {wrong bundle facts element} →
  SourceConditionedElementRequirement {wrong} bundle facts element →
  Elements.ElementDerivation bundle facts element
sourceConditionedElementConclusion {bundle = bundle} {facts = facts} {element = element} input =
  Elements.element-derivation proofOfElement
  where
    proofOfRuleConclusion :
      Algebra.Derivation
        (Elements.ruleGraph bundle) facts (λ _ → ⊤)
        (Algebra.conclusion (Elements.authorityRule (requirement input)))
    proofOfRuleConclusion =
      AtomicImplication.compileAtomicLegalImplication
        (authorityRuleApplication input)
        (authorityRuleDerivationReceipt input)

    proofOfRequired :
      Algebra.Derivation
        (Elements.ruleGraph bundle) facts (λ _ → ⊤)
        (Elements.requiredProposition (requirement input))
    proofOfRequired rewrite authorityRuleConclusionIsRequiredProposition input =
      proofOfRuleConclusion

    proofOfElement :
      Algebra.Derivation
        (Elements.ruleGraph bundle) facts (λ _ → ⊤)
        (Elements.proposition element)
    proofOfElement rewrite requiredPropositionIsExactElement input =
      proofOfRequired

record SourceConditionedViolation
    {state : Status.SemanticCommitmentState}
    (wrong : Ontology.WrongType)
    (bundle : Elements.WrongTypeRuleBundle wrong)
    (facts : Algebra.FactSet) : Set₁ where
  constructor source-conditioned-violation
  field
    applicabilityRule : Algebra.LegalRule
    applicability :
      SourceConditionedApplicability
        (Elements.ruleGraph bundle) facts (λ _ → ⊤) applicabilityRule
    applicabilityWrongTypeMatches : Meet.wrongType (semanticMeet applicability) ≡ wrong
    sourceConditionedRequirements :
      ∀ {element} →
      element Algebra.∈ Elements.elements bundle →
      SourceConditionedElementRequirement bundle facts element
    elementDerivations :
      ∀ {element} →
      element Algebra.∈ Elements.elements bundle →
      Elements.ElementDerivation bundle facts element
    legacyViolationMeet : Violation.ViolationMeetInput state
    legacyViolationWrongTypeMatches :
      Legal.wrongType
        (Violation.receipt (Violation.applicability (Violation.prerequisites legacyViolationMeet)))
      ≡ wrong
    violationReference : String

open SourceConditionedViolation public

legacyViolationProjection :
  ∀ {state wrong bundle facts} →
  SourceConditionedViolation {state} wrong bundle facts →
  Legal.ViolationReceipt
legacyViolationProjection sourceViolation =
  Violation.compileViolationMeet (legacyViolationMeet sourceViolation)

data SemanticMeetAloneProvesLegalApplicability : Set where
data SameWrongTypeEvaluationsDefineRequiredElements : Set where
data ElementSourceMetadataAlonePaysElement : Set where
data AllElementsProvedIgnoresExceptionsDefences : Set where
data SourceRealisedWrongTypeAutomaticallyViolated : Set where
data AtomicFitAutomaticallyEqualsDerivation : Set where

semanticMeetDoesNotAloneProveLegalApplicability : SemanticMeetAloneProvesLegalApplicability → ⊥
semanticMeetDoesNotAloneProveLegalApplicability ()
sameWrongTypeEvaluationsDoNotDefineRequiredElements : SameWrongTypeEvaluationsDefineRequiredElements → ⊥
sameWrongTypeEvaluationsDoNotDefineRequiredElements ()
elementSourceMetadataDoesNotPayElement : ElementSourceMetadataAlonePaysElement → ⊥
elementSourceMetadataDoesNotPayElement ()
allElementsDoNotEraseExceptionsDefences : AllElementsProvedIgnoresExceptionsDefences → ⊥
allElementsDoNotEraseExceptionsDefences ()
sourceRealisedWrongTypeDoesNotAutoViolate : SourceRealisedWrongTypeAutomaticallyViolated → ⊥
sourceRealisedWrongTypeDoesNotAutoViolate ()
atomicFitDoesNotEqualDerivation : AtomicFitAutomaticallyEqualsDerivation → ⊥
atomicFitDoesNotEqualDerivation ()

record SourceConditionedApplicabilityViolationBoundary : Set where
  constructor source-conditioned-applicability-violation-boundary
  field
    semanticMeetRetained : Bool
    applicabilityUsesAtomicSourceConditionedImplication : Bool
    wrongTypeBundleDefinesElementUniverse : Bool
    everyElementRequirementUsesAtomicSourceConditionedImplication : Bool
    everyElementRuleConcludesExactElementProposition : Bool
    atomicFitAndGraphDerivationRemainSeparate : Bool
    legacyAdaptersRemainProjectionOnly : Bool

canonicalSourceConditionedApplicabilityViolationBoundary : SourceConditionedApplicabilityViolationBoundary
canonicalSourceConditionedApplicabilityViolationBoundary =
  source-conditioned-applicability-violation-boundary true true true true true true true
