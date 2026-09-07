module DASHI.Law.SensibLawCausationQualifiedLiabilityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Law.LegalFactualCausationButForExact as ButFor

------------------------------------------------------------------------
-- SENSIBLAW VIOLATION -> CAUSATION -> SCOPE -> LIABILITY BRIDGE
--
-- DASHI-original adapter.  Existing SensibLaw remains the owner of
-- applicability/violation/liability/remedy records.  This module does not
-- redefine LiabilityReceipt.  Instead it exposes a causation-qualified input
-- that can be required by negligence-like consumers before an existing
-- LiabilityReceipt is accepted downstream.
------------------------------------------------------------------------

record ViolationCausationWeld : Set₁ where
  constructor violationCausationWeld
  field
    violation : Legal.ViolationReceipt
    question : ButFor.LegalButForQuestion
    sameBreachReferenceReceipt : Set
    sameEventOrOccurrenceReceipt : Set
    sameParticularHarmContextReceipt : Set
    weldReference : String

open ViolationCausationWeld public

record CausationQualifiedLiabilityInput : Set₁ where
  constructor causationQualifiedLiabilityInput
  field
    weld : ViolationCausationWeld
    factualCausation : ButFor.FactualCausationReceipt (question weld)
    scopeOfLiability : ButFor.ScopeOfLiabilityReceipt factualCausation
    causationProof : ButFor.CausationProofReceipt factualCausation
    qualificationReference : String

open CausationQualifiedLiabilityInput public

record CausationQualifiedLiabilityReceipt : Set₁ where
  constructor causationQualifiedLiabilityReceipt
  field
    qualifiedInput : CausationQualifiedLiabilityInput
    liability : Legal.LiabilityReceipt
    sameViolationReceipt :
      Legal.violationReceipt liability
      ≡ violation (weld qualifiedInput)
    liabilityResolutionReference : String

open CausationQualifiedLiabilityReceipt public

------------------------------------------------------------------------
-- Consumer policy: not every WrongType necessarily has a causation element.
-- The consumer/legal-rule layer declares whether this bridge is required.
------------------------------------------------------------------------

data CausationGateRequirement : Set where
  causationRequired
  causationNotRequired
  causationRequirementUnresolved
  : CausationGateRequirement

record LiabilityConsumerCausationPolicy : Set where
  constructor liabilityConsumerCausationPolicy
  field
    wrongTypeReference : String
    requirement : CausationGateRequirement
    legalRuleReference : String
    authorityReceipt : Set

open LiabilityConsumerCausationPolicy public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data EveryViolationRequiresButForCausation : Set where
data ViolationAutomaticallySuppliesCausationWeld : Set where
data FactualCausationAutomaticallySuppliesScope : Set where
data ExistingLiabilityReceiptRetroactivelyProvesCausation : Set where
data CausationPolicyMayBeInferredFromParserSyntax : Set where

everyViolationDoesNotRequireButForByTypeAlone :
  EveryViolationRequiresButForCausation → ⊥
everyViolationDoesNotRequireButForByTypeAlone ()

violationDoesNotAutoSupplyCausationWeld :
  ViolationAutomaticallySuppliesCausationWeld → ⊥
violationDoesNotAutoSupplyCausationWeld ()

factualCausationDoesNotAutoSupplyScope :
  FactualCausationAutomaticallySuppliesScope → ⊥
factualCausationDoesNotAutoSupplyScope ()

existingLiabilityDoesNotRetroProveCausation :
  ExistingLiabilityReceiptRetroactivelyProvesCausation → ⊥
existingLiabilityDoesNotRetroProveCausation ()

parserSyntaxDoesNotChooseCausationPolicy :
  CausationPolicyMayBeInferredFromParserSyntax → ⊥
parserSyntaxDoesNotChooseCausationPolicy ()

record CausationQualifiedLiabilityBoundary : Set where
  constructor causationQualifiedLiabilityBoundary
  field
    causationGateIsConsumerDeclared : Bool
    causationGateIsConsumerDeclaredIsTrue : causationGateIsConsumerDeclared ≡ true
    factualCausationAndScopeRemainDistinct : Bool
    factualCausationAndScopeRemainDistinctIsTrue :
      factualCausationAndScopeRemainDistinct ≡ true
    oldLiabilityReceiptDefinitionReplaced : Bool
    oldLiabilityReceiptDefinitionReplacedIsFalse :
      oldLiabilityReceiptDefinitionReplaced ≡ false

canonicalCausationQualifiedLiabilityBoundary : CausationQualifiedLiabilityBoundary
canonicalCausationQualifiedLiabilityBoundary =
  causationQualifiedLiabilityBoundary true refl true refl false refl
