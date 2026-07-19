module DASHI.Context.ContextInvariantTests where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Context.ContextEnvelopeInvariant
open import DASHI.Context.NarrativeProjectionBoundary
import DASHI.Context.RoleScopedAccessContract as Access
import DASHI.Context.PublicPowerContextBridge as Public

------------------------------------------------------------------------
-- Regression witnesses: incomplete content is valid; context is attached;
-- projections are explicit, non-canonical, loss-declaring, and do not gain
-- diagnosis or automatic legal authority.

minimalArtifact : Artifact
minimalArtifact =
  record
    { artifactId = "fragment-001"
    ; canonicalText = ""
    }

minimalContextBoundArtifact : ContextBoundArtifact
minimalContextBoundArtifact =
  record
    { artifact = minimalArtifact
    ; envelope = canonicalProtectedSubjectEnvelope
    ; envelopeAttached = true
    ; envelopeAttachedIsTrue = refl
    }

minimalLossProfile : LossProfile
minimalLossProfile =
  record
    { omittedArtifactIds = []
    ; omittedContextKinds = []
    ; compressionDescription = "minimal projection with no omitted source"
    ; lossDeclared = true
    ; lossDeclaredIsTrue = refl
    }

minimalExplicitProjection : NarrativeProjection
minimalExplicitProjection =
  record
    { sourceArtifacts = minimalContextBoundArtifact ∷ []
    ; audience = protectedSubject
    ; projectionKind = timelineView
    ; inferenceLevel = none
    ; renderedText = ""
    ; lossProfile = minimalLossProfile
    ; explicitlyRequested = true
    ; explicitlyRequestedIsTrue = refl
    ; nonCanonical = true
    ; nonCanonicalIsTrue = refl
    ; contextReferencesRetained = true
    ; contextReferencesRetainedIsTrue = refl
    ; noDiagnosisAuthority = true
    ; noDiagnosisAuthorityIsTrue = refl
    ; noAutomaticLegalCharacterisation = true
    ; noAutomaticLegalCharacterisationIsTrue = refl
    }

minimalArtifactContextIntegrity :
  envelopeAttached minimalContextBoundArtifact ≡ true
minimalArtifactContextIntegrity =
  contextIntegrity minimalContextBoundArtifact

minimalProjectionWasRequested :
  explicitlyRequested minimalExplicitProjection ≡ true
minimalProjectionWasRequested =
  projectionRequiresRequest minimalExplicitProjection

minimalProjectionIsNotCanonical :
  nonCanonical minimalExplicitProjection ≡ true
minimalProjectionIsNotCanonical =
  projectionIsNonCanonical minimalExplicitProjection

minimalProjectionRetainsItsContext :
  contextReferencesRetained minimalExplicitProjection ≡ true
minimalProjectionRetainsItsContext =
  projectionRetainsContext minimalExplicitProjection

protectedSubjectNoForcedNarrative :
  noForcedNarrative canonicalProtectedSubjectEnvelope ≡ true
protectedSubjectNoForcedNarrative =
  noForcedNarrativeIsTrue canonicalProtectedSubjectEnvelope

protectedSubjectAmbiguityPermitted :
  ambiguityPermitted canonicalProtectedSubjectEnvelope ≡ true
protectedSubjectAmbiguityPermitted =
  ambiguityPermittedIsTrue canonicalProtectedSubjectEnvelope

clinicianAccessRequiresConsent :
  Access.subjectConsent Access.canonicalClinicianGrant ≡ true
clinicianAccessRequiresConsent =
  Access.subjectConsentIsTrue Access.canonicalClinicianGrant

advocateAccessIsRevocable :
  Access.revocable Access.canonicalAdvocateGrant ≡ true
advocateAccessIsRevocable =
  Access.revocableIsTrue Access.canonicalAdvocateGrant

microPromisesRemainFirstClass :
  Public.microPromisesAreFirstClass Public.canonicalEmptySmallTrustLedger ≡ true
microPromisesRemainFirstClass =
  Public.microPromisesAreFirstClassIsTrue
    Public.canonicalEmptySmallTrustLedger
