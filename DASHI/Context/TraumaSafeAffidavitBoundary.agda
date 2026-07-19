module DASHI.Context.TraumaSafeAffidavitBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Context.ContextEnvelopeInvariant
open import DASHI.Context.NarrativeProjectionBoundary

------------------------------------------------------------------------
-- Court-facing structure without forced retelling.
--
-- The affidavit lane separates observation, report, inference, and unknown;
-- permits approximate chronology; permits details to remain sealed; and
-- requires every clause to retain an event and context reference.


data ClaimKind : Set where
  observed : ClaimKind
  reported : ClaimKind
  inferred : ClaimKind
  unknownClaim : ClaimKind


data DetailDisposition : Set where
  included : DetailDisposition
  redactedDetail : DetailDisposition
  sealedAnnex : DetailDisposition
  notReady : DetailDisposition

record AffidavitClause : Set where
  field
    clauseId : String
    sourceArtifact : ContextBoundArtifact
    claimKind : ClaimKind
    clauseText : String
    detailDisposition : DetailDisposition

    contextReferenceRetained : Bool
    contextReferenceRetainedIsTrue :
      contextReferenceRetained ≡ true

    userAuthoredOrApproved : Bool
    userAuthoredOrApprovedIsTrue :
      userAuthoredOrApproved ≡ true

    uncertaintyPreserved : Bool
    uncertaintyPreservedIsTrue : uncertaintyPreserved ≡ true

    noAutomaticLegalCharacterisation : Bool
    noAutomaticLegalCharacterisationIsTrue :
      noAutomaticLegalCharacterisation ≡ true

    noGraphicRetellingRequirement : Bool
    noGraphicRetellingRequirementIsTrue :
      noGraphicRetellingRequirement ≡ true

open AffidavitClause public

record AffidavitBundle : Set where
  field
    clauses : List AffidavitClause
    chronologyProjection : NarrativeProjection
    exhibitArtifactIds : List String
    sealedAnnexArtifactIds : List String

    chronologyIsNonCanonical :
      nonCanonical chronologyProjection ≡ true

    chronologyRetainsContext :
      contextReferencesRetained chronologyProjection ≡ true

    crossExaminationKindsSeparated : Bool
    crossExaminationKindsSeparatedIsTrue :
      crossExaminationKindsSeparated ≡ true

    rawArtifactsUnchanged : Bool
    rawArtifactsUnchangedIsTrue : rawArtifactsUnchanged ≡ true

    reInjuryMinimisationRequired : Bool
    reInjuryMinimisationRequiredIsTrue :
      reInjuryMinimisationRequired ≡ true

open AffidavitBundle public

clauseRetainsContext :
  (c : AffidavitClause) →
  contextReferenceRetained c ≡ true
clauseRetainsContext c = contextReferenceRetainedIsTrue c

clausePreservesUncertainty :
  (c : AffidavitClause) →
  uncertaintyPreserved c ≡ true
clausePreservesUncertainty c = uncertaintyPreservedIsTrue c
