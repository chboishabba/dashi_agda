module DASHI.Context.ContextEnvelopeInvariant where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Context is part of the carrier, not optional metadata.
--
-- The original protected-subject use case requires that fragmented,
-- approximate, disputed, or presently unsafe material remain admissible
-- without being rewritten into a single coherent narrative.  The same
-- invariant scales to journalism, comedy, public administration, legal
-- advocacy, and institutional memory.


data TemporalPrecision : Set where
  exact : TemporalPrecision
  approximate : TemporalPrecision
  relative : TemporalPrecision
  unknown : TemporalPrecision


data EpistemicStatus : Set where
  knownThen : EpistemicStatus
  knownLater : EpistemicStatus
  disputed : EpistemicStatus
  partial : EpistemicStatus
  unsafeToRecall : EpistemicStatus
  notKnown : EpistemicStatus


data VenueKind : Set where
  privateConversation : VenueKind
  clinicalEncounter : VenueKind
  legalProceeding : VenueKind
  comedyPerformance : VenueKind
  journalisticInterview : VenueKind
  publicAdministration : VenueKind
  documentaryArtifact : VenueKind
  otherVenue : VenueKind


data Opacity : Set where
  openDetail : Opacity
  redacted : Opacity
  sealed : Opacity

record ContextEnvelope : Set where
  field
    createdAt : String
    temporalPrecision : TemporalPrecision
    venue : VenueKind
    intendedAudience : List String
    captureSource : String
    epistemicStatus : EpistemicStatus
    relationalContext : List String
    interpretationLimits : List String
    opacity : Opacity

    contextRequired : Bool
    contextRequiredIsTrue : contextRequired ≡ true

    noForcedNarrative : Bool
    noForcedNarrativeIsTrue : noForcedNarrative ≡ true

    ambiguityPermitted : Bool
    ambiguityPermittedIsTrue : ambiguityPermitted ≡ true

    laterFactsDoNotOverwriteThen : Bool
    laterFactsDoNotOverwriteThenIsTrue :
      laterFactsDoNotOverwriteThen ≡ true

open ContextEnvelope public

record Artifact : Set where
  field
    artifactId : String
    canonicalText : String

open Artifact public

record ContextBoundArtifact : Set where
  field
    artifact : Artifact
    envelope : ContextEnvelope
    envelopeAttached : Bool
    envelopeAttachedIsTrue : envelopeAttached ≡ true

open ContextBoundArtifact public

contextIntegrity :
  (x : ContextBoundArtifact) →
  envelopeAttached x ≡ true
contextIntegrity x = envelopeAttachedIsTrue x

canonicalProtectedSubjectEnvelope : ContextEnvelope
canonicalProtectedSubjectEnvelope =
  record
    { createdAt = "unspecified"
    ; temporalPrecision = unknown
    ; venue = privateConversation
    ; intendedAudience = "protected subject" ∷ []
    ; captureSource = "user-controlled capture"
    ; epistemicStatus = partial
    ; relationalContext = []
    ; interpretationLimits =
        "do not infer motive"
        ∷ "do not infer diagnosis"
        ∷ "do not infer legal characterisation"
        ∷ []
    ; opacity = sealed
    ; contextRequired = true
    ; contextRequiredIsTrue = refl
    ; noForcedNarrative = true
    ; noForcedNarrativeIsTrue = refl
    ; ambiguityPermitted = true
    ; ambiguityPermittedIsTrue = refl
    ; laterFactsDoNotOverwriteThen = true
    ; laterFactsDoNotOverwriteThenIsTrue = refl
    }

canonicalPublicConversationEnvelope : ContextEnvelope
canonicalPublicConversationEnvelope =
  record
    { createdAt = "unspecified"
    ; temporalPrecision = exact
    ; venue = journalisticInterview
    ; intendedAudience = "public audience" ∷ []
    ; captureSource = "recorded interview"
    ; epistemicStatus = knownThen
    ; relationalContext =
        "host"
        ∷ "guest"
        ∷ "production team"
        ∷ []
    ; interpretationLimits =
        "excerpt is not the complete conversation"
        ∷ "comedic framing may be active"
        ∷ "later reuse must retain original audience and venue"
        ∷ []
    ; opacity = openDetail
    ; contextRequired = true
    ; contextRequiredIsTrue = refl
    ; noForcedNarrative = true
    ; noForcedNarrativeIsTrue = refl
    ; ambiguityPermitted = true
    ; ambiguityPermittedIsTrue = refl
    ; laterFactsDoNotOverwriteThen = true
    ; laterFactsDoNotOverwriteThenIsTrue = refl
    }
