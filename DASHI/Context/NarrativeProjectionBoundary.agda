module DASHI.Context.NarrativeProjectionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Context.ContextEnvelopeInvariant

------------------------------------------------------------------------
-- A projection is a reversible, audience-scoped view over canonical
-- artifacts.  It is never the canonical record and cannot silently claim
-- completeness, certainty, diagnosis, legal guilt, or a unified story.


data AudienceRole : Set where
  protectedSubject : AudienceRole
  supportOperator : AudienceRole
  clinician : AudienceRole
  advocate : AudienceRole
  journalist : AudienceRole
  publicOfficial : AudienceRole
  publicAudience : AudienceRole


data ProjectionKind : Set where
  timelineView : ProjectionKind
  evidenceIndexView : ProjectionKind
  clinicalHandoffView : ProjectionKind
  advocateChronologyView : ProjectionKind
  affidavitView : ProjectionKind
  publicPromiseView : ProjectionKind
  mediaExcerptView : ProjectionKind


data InferenceLevel : Set where
  none : InferenceLevel
  userAuthoredOnly : InferenceLevel
  explicitlyLinked : InferenceLevel

record LossProfile : Set where
  field
    omittedArtifactIds : List String
    omittedContextKinds : List String
    compressionDescription : String
    lossDeclared : Bool
    lossDeclaredIsTrue : lossDeclared ≡ true

open LossProfile public

record NarrativeProjection : Set where
  field
    sourceArtifacts : List ContextBoundArtifact
    audience : AudienceRole
    projectionKind : ProjectionKind
    inferenceLevel : InferenceLevel
    renderedText : String
    lossProfile : LossProfile

    explicitlyRequested : Bool
    explicitlyRequestedIsTrue : explicitlyRequested ≡ true

    nonCanonical : Bool
    nonCanonicalIsTrue : nonCanonical ≡ true

    contextReferencesRetained : Bool
    contextReferencesRetainedIsTrue :
      contextReferencesRetained ≡ true

    noDiagnosisAuthority : Bool
    noDiagnosisAuthorityIsTrue : noDiagnosisAuthority ≡ true

    noAutomaticLegalCharacterisation : Bool
    noAutomaticLegalCharacterisationIsTrue :
      noAutomaticLegalCharacterisation ≡ true

open NarrativeProjection public

projectionIsNonCanonical :
  (p : NarrativeProjection) →
  nonCanonical p ≡ true
projectionIsNonCanonical p = nonCanonicalIsTrue p

projectionRetainsContext :
  (p : NarrativeProjection) →
  contextReferencesRetained p ≡ true
projectionRetainsContext p = contextReferencesRetainedIsTrue p

projectionRequiresRequest :
  (p : NarrativeProjection) →
  explicitlyRequested p ≡ true
projectionRequiresRequest p = explicitlyRequestedIsTrue p

canonicalNoLossProfile : LossProfile
canonicalNoLossProfile =
  record
    { omittedArtifactIds = []
    ; omittedContextKinds = []
    ; compressionDescription = "no compression"
    ; lossDeclared = true
    ; lossDeclaredIsTrue = refl
    }
