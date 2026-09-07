module DASHI.Law.SensibLawSpacyButForBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as SpacyBridge
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as EvidencePNF
import DASHI.Law.LegalFactualCausationButForExact as ButFor

------------------------------------------------------------------------
-- SENSIBLAW spaCy / PNF -> LEGAL BUT-FOR BRIDGE
--
-- DASHI-original bridge.
--
-- Shared dependency parsing remains domain-neutral.  In particular, no raw
-- DependencyShape is reinterpreted as a legal causation relation here.
-- Parser observations yield only candidate semantic material.  A legal but-for
-- question can be constructed downstream only after semantic resolution,
-- evidential-PNF correspondence, world/fact resolution, and legal-authority
-- receipts are supplied independently.
------------------------------------------------------------------------

data CounterfactualCandidateKind : Set where
  possibleActualConduct : CounterfactualCandidateKind
  possibleCompliantConduct : CounterfactualCandidateKind
  possibleParticularHarm : CounterfactualCandidateKind
  possibleCounterfactualRelation : CounterfactualCandidateKind
  unresolvedCounterfactualCandidate : CounterfactualCandidateKind


record ParsedButForCandidate : Set where
  constructor parsedButForCandidate
  field
    sourceFragment : SpacyBridge.CandidateSemanticFragment
    kind : CounterfactualCandidateKind
    breachReferenceCandidate : String
    harmReferenceCandidate : String
    reading : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open ParsedButForCandidate public

record ParsedButForCandidateFibre : Set where
  constructor parsedButForCandidateFibre
  field
    candidates : List ParsedButForCandidate
    fibreReference : String

open ParsedButForCandidateFibre public

------------------------------------------------------------------------
-- Reviewed correspondence layer.
------------------------------------------------------------------------

record ReviewedButForSemanticCorrespondence : Set₁ where
  constructor reviewedButForSemanticCorrespondence
  field
    parserFibre : SpacyBridge.CandidateSemanticFibre
    parserResolution : SpacyBridge.SemanticResolutionReceipt parserFibre
    evidenceAssertion : EvidencePNF.PredicateNormalAssertion
    evidenceCorrespondence :
      SpacyBridge.ResolvedCandidateToEvidencePNF parserResolution evidenceAssertion

    proposedBreachReference : String
    proposedCompliantConductReference : String
    proposedParticularHarmReference : String
    proposedCounterfactualRelationReference : String

    semanticReviewerReference : String
    parserStillNotWorldAuthority : Bool
    parserStillNotWorldAuthorityIsTrue :
      parserStillNotWorldAuthority ≡ true

open ReviewedButForSemanticCorrespondence public

------------------------------------------------------------------------
-- Promotion prerequisites.
--
-- These receipts are intentionally external to the parser correspondence.
-- They are what prevents parser syntax from manufacturing world facts or law.
------------------------------------------------------------------------

record ButForPromotionReceipts : Set where
  constructor butForPromotionReceipts
  field
    occurrenceResolutionReceipt : Set
    breachResolutionReceipt : Set
    compliantConductResolutionReceipt : Set
    particularHarmIdentityReceipt : Set
    counterfactualWorldResolutionReceipt : Set
    heldFixedJustificationReceipt : Set
    causalIdentificationReceipt : Set
    legalAuthorityReceipt : Set
    jurisdictionApplicabilityReceipt : Set
    resolverReference : String

open ButForPromotionReceipts public

record ReviewedParserToLegalButForQuestion : Set₁ where
  constructor reviewedParserToLegalButForQuestion
  field
    semanticCorrespondence : ReviewedButForSemanticCorrespondence
    promotionReceipts : ButForPromotionReceipts
    question : ButFor.LegalButForQuestion

    breachReferenceMatchesQuestion : Set
    compliantConductReferenceMatchesQuestion : Set
    harmReferenceMatchesQuestion : Set
    counterfactualReferenceMatchesQuestion : Set

    bridgeReference : String

open ReviewedParserToLegalButForQuestion public

------------------------------------------------------------------------
-- Candidate constructors deliberately preserve generic parser semantics.
------------------------------------------------------------------------

counterfactualRelationCandidate :
  SpacyBridge.CandidateSemanticFragment →
  String → String → String →
  ParsedButForCandidate
counterfactualRelationCandidate fragment breachRef harmRef reading =
  parsedButForCandidate
    fragment
    possibleCounterfactualRelation
    breachRef
    harmRef
    reading
    true
    refl

harmCandidate :
  SpacyBridge.CandidateSemanticFragment →
  String → String →
  ParsedButForCandidate
harmCandidate fragment harmRef reading =
  parsedButForCandidate
    fragment
    possibleParticularHarm
    "unresolved-breach"
    harmRef
    reading
    true
    refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DependencyShapeAutomaticallyButForCausation : Set where
data ParserCandidateAutomaticallyWorldFact : Set where
data ParserCandidateAutomaticallyLegalAuthority : Set where
data SemanticResolutionAutomaticallyCausalIdentification : Set where
data EvidencePNFAutomaticallyLegalConclusion : Set where
data ReverseParserSupportIsInverseLegalDerivation : Set where

dependencyShapeDoesNotAutoMeanButFor :
  DependencyShapeAutomaticallyButForCausation → ⊥
dependencyShapeDoesNotAutoMeanButFor ()

parserCandidateDoesNotAutoBecomeWorldFact :
  ParserCandidateAutomaticallyWorldFact → ⊥
parserCandidateDoesNotAutoBecomeWorldFact ()

parserCandidateDoesNotAutoBecomeLegalAuthority :
  ParserCandidateAutomaticallyLegalAuthority → ⊥
parserCandidateDoesNotAutoBecomeLegalAuthority ()

semanticResolutionDoesNotAutoIdentifyCausation :
  SemanticResolutionAutomaticallyCausalIdentification → ⊥
semanticResolutionDoesNotAutoIdentifyCausation ()

evidencePNFDoesNotAutoBecomeLegalConclusion :
  EvidencePNFAutomaticallyLegalConclusion → ⊥
evidencePNFDoesNotAutoBecomeLegalConclusion ()

reverseParserSupportIsNotInverseLegalDerivation :
  ReverseParserSupportIsInverseLegalDerivation → ⊥
reverseParserSupportIsNotInverseLegalDerivation ()

record SensibLawButForParserBoundary : Set where
  constructor sensibLawButForParserBoundary
  field
    sharedParserHasLegalMode : Bool
    sharedParserHasLegalModeIsFalse : sharedParserHasLegalMode ≡ false
    rawDependencyMeansLegalCausation : Bool
    rawDependencyMeansLegalCausationIsFalse : rawDependencyMeansLegalCausation ≡ false
    parserOutputIsWorldAuthority : Bool
    parserOutputIsWorldAuthorityIsFalse : parserOutputIsWorldAuthority ≡ false
    parserOutputIsLegalAuthority : Bool
    parserOutputIsLegalAuthorityIsFalse : parserOutputIsLegalAuthority ≡ false
    reviewedCorrespondenceMayFeedLegalConsumer : Bool
    reviewedCorrespondenceMayFeedLegalConsumerIsTrue :
      reviewedCorrespondenceMayFeedLegalConsumer ≡ true

canonicalSensibLawButForParserBoundary : SensibLawButForParserBoundary
canonicalSensibLawButForParserBoundary =
  sensibLawButForParserBoundary false refl false refl false refl false refl true refl
