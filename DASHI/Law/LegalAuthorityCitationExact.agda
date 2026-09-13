module DASHI.Law.LegalAuthorityCitationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC LEGAL AUTHORITY CITATION / CLAIM-BOUNDARY CARRIER
--
-- Promotes the reusable source discipline already exercised in the Mabo lane:
-- source identification, exact locator, authority role, proposition boundary,
-- and consumer use remain distinct coordinates.
--
-- A citation does not by itself establish the truth, binding force, ratio,
-- applicability, jurisdictional fit, or final legal characterisation.
------------------------------------------------------------------------

data LegalSourceKind : Set where
  constitution : LegalSourceKind
  legislation : LegalSourceKind
  regulation : LegalSourceKind
  judgment : LegalSourceKind
  treaty : LegalSourceKind
  parliamentaryRecord : LegalSourceKind
  executiveInstrument : LegalSourceKind
  officialGuidance : LegalSourceKind
  academicCommentary : LegalSourceKind
  publicStatement : LegalSourceKind
  evidentiaryArtifact : LegalSourceKind


data LegalAuthorityRole : Set where
  bindingPrimaryAuthority : LegalAuthorityRole
  persuasivePrimaryAuthority : LegalAuthorityRole
  primaryTextEvidence : LegalAuthorityRole
  legislativeHistory : LegalAuthorityRole
  officialInterpretiveMaterial : LegalAuthorityRole
  secondaryCommentary : LegalAuthorityRole
  factualProvenanceOnly : LegalAuthorityRole
  allegationSourceOnly : LegalAuthorityRole
  responseSourceOnly : LegalAuthorityRole
  unresolvedAuthorityRole : LegalAuthorityRole


data LegalIdentifier : Set where
  neutralCitation : String → LegalIdentifier
  authorisedReportCitation : String → LegalIdentifier
  statutoryCitation : String → LegalIdentifier
  treatyCitation : String → LegalIdentifier
  parliamentaryCitation : String → LegalIdentifier
  officialDocumentIdentifier : String → LegalIdentifier
  canonicalLegalURL : String → LegalIdentifier
  bibliographicLegalFallback : String → LegalIdentifier

record LegalCitation : Set where
  constructor legal-citation
  field
    sourceKind : LegalSourceKind
    authorityRole : LegalAuthorityRole
    jurisdiction : String
    issuingBodyOrCourt : String
    title : String
    year : Nat
    identifier : LegalIdentifier
    exactLocator : String
    boundedProposition : String
    bindingForceClaimed : Bool
    bindingForceClaimedIsFalseUnlessSeparatelyProved : bindingForceClaimed ≡ false

open LegalCitation public

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record LegalAuthorityUseReceipt (citation : LegalCitation) : Set where
  constructor legal-authority-use-receipt
  field
    selectedConsumer : String
    propositionUsed : String
    authorityClassificationReviewed : Bool
    authorityClassificationReviewedIsTrue : authorityClassificationReviewed ≡ true
    jurisdictionalFitReviewed : Bool
    jurisdictionalFitReviewedIsTrue : jurisdictionalFitReviewed ≡ true
    propositionFitReviewed : Bool
    propositionFitReviewedIsTrue : propositionFitReviewed ≡ true
    finalCharacterisationImportedFromCitation : Bool
    finalCharacterisationImportedFromCitationIsFalse :
      finalCharacterisationImportedFromCitation ≡ false

open LegalAuthorityUseReceipt public

record LegalCitationBoundary : Set where
  constructor legal-citation-boundary
  field
    citationEstablishesTruth : Bool
    citationEstablishesTruthIsFalse : citationEstablishesTruth ≡ false
    citationEstablishesBindingForce : Bool
    citationEstablishesBindingForceIsFalse : citationEstablishesBindingForce ≡ false
    citationEstablishesApplicability : Bool
    citationEstablishesApplicabilityIsFalse : citationEstablishesApplicability ≡ false
    allegationEqualsAdjudication : Bool
    allegationEqualsAdjudicationIsFalse : allegationEqualsAdjudication ≡ false
    responseEqualsDisproof : Bool
    responseEqualsDisproofIsFalse : responseEqualsDisproof ≡ false

open LegalCitationBoundary public

canonicalLegalCitationBoundary : LegalCitationBoundary
canonicalLegalCitationBoundary =
  legal-citation-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
