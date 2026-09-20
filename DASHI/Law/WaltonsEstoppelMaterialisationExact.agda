module DASHI.Law.WaltonsEstoppelMaterialisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.AustralianContractsLegalFollowExact as Contracts
import DASHI.Law.SensibLawLegalFollowProofSearchBridgeExact as LegalFollow
import DASHI.Law.SensibLawRuntimeWrongTypeElementFrontierExact as WrongTypeFrontier
import DASHI.Interop.SemanticReaderElucidatoryConeExact as Reader

------------------------------------------------------------------------
-- WALTONS / ESTOPPEL MATERIALISATION
--
-- This owner formalises the *research/materialisation* boundary for a new
-- Australian contract doctrine.  It deliberately does not claim that the
-- labels below are a closed mechanical test of equitable estoppel.  They are
-- typed research requirements that LegalFollow must source, review, and weld
-- before any WrongType/legal-element payment can be claimed.
------------------------------------------------------------------------

data EstoppelResearchRole : Set where
  assumptionOrExpectation : EstoppelResearchRole
  inducementOrAdoption : EstoppelResearchRole
  relianceOrAction : EstoppelResearchRole
  detriment : EstoppelResearchRole
  unconscionableDeparture : EstoppelResearchRole
  reliefResponsiveToEquity : EstoppelResearchRole

record EstoppelResearchRequirement : Set where
  constructor estoppelResearchRequirement
  field
    role : EstoppelResearchRole
    requirementReference : String
    sourceRequired : Bool
    sourceRequiredIsTrue : sourceRequired ≡ true
    reviewRequired : Bool
    reviewRequiredIsTrue : reviewRequired ≡ true
    requirementIsLegalConclusion : Bool
    requirementIsLegalConclusionIsFalse :
      requirementIsLegalConclusion ≡ false

open EstoppelResearchRequirement public

record WaltonsEstoppelMaterialisation : Set₁ where
  constructor waltonsEstoppelMaterialisation
  field
    conceptReference : String
    doctrineReference : String
    primaryCaseReference : String
    primaryCaseCitation : String
    jurisdictionReference : String
    contractTrace : Contracts.AustralianContractFollowTrace
    researchRequirements : List EstoppelResearchRequirement

    legalFollowSourceReceipt : Set
    authorityReviewReceipt : Set
    propositionReviewReceipt : Set

    contextCardCreatesAuthority : Bool
    contextCardCreatesAuthorityIsFalse :
      contextCardCreatesAuthority ≡ false

    qidIdentityCreatesApplicability : Bool
    qidIdentityCreatesApplicabilityIsFalse :
      qidIdentityCreatesApplicability ≡ false

    researchRequirementEqualsPaidWrongTypeElement : Bool
    researchRequirementEqualsPaidWrongTypeElementIsFalse :
      researchRequirementEqualsPaidWrongTypeElement ≡ false

    acquisitionEqualsDoctrinePayment : Bool
    acquisitionEqualsDoctrinePaymentIsFalse :
      acquisitionEqualsDoctrinePayment ≡ false

    materialisationCandidateOnly : Bool
    materialisationCandidateOnlyIsTrue :
      materialisationCandidateOnly ≡ true

open WaltonsEstoppelMaterialisation public

------------------------------------------------------------------------
-- Existing reader and WrongType machinery remain downstream owners.
------------------------------------------------------------------------

ReaderIntent : Set
ReaderIntent = Reader.SemanticIntent

WrongTypeElementBoundary : Set
WrongTypeElementBoundary = WrongTypeFrontier.RuntimeWrongTypeElementBoundary

wrongTypeElementBoundaryPaid : WrongTypeElementBoundary
wrongTypeElementBoundaryPaid =
  WrongTypeFrontier.canonicalRuntimeWrongTypeElementBoundary

LegalFollowBoundary : Set
LegalFollowBoundary = LegalFollow.LegalFollowProofSearchBoundary

legalFollowBoundaryPaid : LegalFollowBoundary
legalFollowBoundaryPaid =
  LegalFollow.canonicalLegalFollowProofSearchBoundary

------------------------------------------------------------------------
-- Canonical narrow fixture.
------------------------------------------------------------------------

waltonsTrace : Contracts.AustralianContractFollowTrace
waltonsTrace =
  Contracts.australianContractFollowTrace
    "doctrine:au:contract:estoppel"
    (Contracts.contractTraceNode
      "case:au:hca:1988:7"
      "Waltons Stores (Interstate) Ltd v Maher"
      Contracts.estoppel
      "AU"
      "court:HCA"
      "1988"
      Contracts.primaryCaseLaw
      Contracts.official
      "[1988] HCA 7; 164 CLR 387"
      true refl
      false refl
      ∷ [])
    []
    true refl
    true refl
    true refl
    false refl

waltonsAssumptionRequirement : EstoppelResearchRequirement
waltonsAssumptionRequirement =
  estoppelResearchRequirement
    assumptionOrExpectation
    "requirement:estoppel:assumption"
    true refl
    true refl
    false refl

waltonsRelianceRequirement : EstoppelResearchRequirement
waltonsRelianceRequirement =
  estoppelResearchRequirement
    relianceOrAction
    "requirement:estoppel:reliance"
    true refl
    true refl
    false refl

waltonsDetrimentRequirement : EstoppelResearchRequirement
waltonsDetrimentRequirement =
  estoppelResearchRequirement
    detriment
    "requirement:estoppel:detriment"
    true refl
    true refl
    false refl

waltonsUnconscionabilityRequirement : EstoppelResearchRequirement
waltonsUnconscionabilityRequirement =
  estoppelResearchRequirement
    unconscionableDeparture
    "requirement:estoppel:unconscionability"
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LexicalDefinitionAutomaticallyLegalConstruction : Set where
data ContextLinkAutomaticallyEvidencePayment : Set where
data WaltonsCitationAutomaticallyPaysEveryEstoppelRequirement : Set where
data EstoppelGraphAutomaticallyDeterminesRelief : Set where

lexicalDefinitionDoesNotCreateLegalConstruction :
  LexicalDefinitionAutomaticallyLegalConstruction → ⊥
lexicalDefinitionDoesNotCreateLegalConstruction ()

contextLinkDoesNotPayEvidence :
  ContextLinkAutomaticallyEvidencePayment → ⊥
contextLinkDoesNotPayEvidence ()

waltonsCitationDoesNotPayEveryRequirement :
  WaltonsCitationAutomaticallyPaysEveryEstoppelRequirement → ⊥
waltonsCitationDoesNotPayEveryEstoppelRequirement ()

estoppelGraphDoesNotDetermineRelief :
  EstoppelGraphAutomaticallyDeterminesRelief → ⊥
estoppelGraphDoesNotDetermineRelief ()

record WaltonsEstoppelBoundary : Set where
  constructor waltonsEstoppelBoundary
  field
    genericLegalFollowReused : Bool
    genericLegalFollowReusedIsTrue : genericLegalFollowReused ≡ true
    genericWrongTypeFrontierReused : Bool
    genericWrongTypeFrontierReusedIsTrue :
      genericWrongTypeFrontierReused ≡ true
    estoppelSpecificRuntimeRequired : Bool
    estoppelSpecificRuntimeRequiredIsFalse :
      estoppelSpecificRuntimeRequired ≡ false
    sourceAcquisitionCreatesLegalTruth : Bool
    sourceAcquisitionCreatesLegalTruthIsFalse :
      sourceAcquisitionCreatesLegalTruth ≡ false

canonicalWaltonsEstoppelBoundary : WaltonsEstoppelBoundary
canonicalWaltonsEstoppelBoundary =
  waltonsEstoppelBoundary
    true refl
    true refl
    false refl
    false refl
