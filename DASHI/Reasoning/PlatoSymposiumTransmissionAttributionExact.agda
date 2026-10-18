module DASHI.Reasoning.PlatoSymposiumTransmissionAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Reasoning.JMDAristotleSymposiumSourceAtlasExact as Source

------------------------------------------------------------------------
-- PLATO SYMPOSIUM TRANSMISSION / ATTRIBUTION
------------------------------------------------------------------------

existingAttributionOwnersReused : Bool
existingAttributionOwnersReused = true

data TransmissionRole : Set where
  dialogueAuthorRole : TransmissionRole
  dramaticSpeakerRole : TransmissionRole
  reportedTeacherRole : TransmissionRole
  formalisationAuthorRole : TransmissionRole
  dashiBridgeAuthorRole : TransmissionRole

data ClaimTransmissionKind : Set where
  ownArgument : ClaimTransmissionKind
  reportedTeaching : ClaimTransmissionKind
  quotedOrReconstructedClaim : ClaimTransmissionKind
  formalisedProposition : ClaimTransmissionKind
  structuralCrossPollination : ClaimTransmissionKind

record TransmissionStage : Set where
  constructor transmission-stage
  field
    actorReference : String
    role : TransmissionRole
    claimKind : ClaimTransmissionKind
    sourceBounded : Bool

open TransmissionStage public

record TransmissionPath : Set where
  constructor transmission-path
  field
    dialogueSource : Attribution.AttributedSource
    dialogueAuthor : TransmissionStage
    immediateSpeaker : TransmissionStage
    reportedSource : TransmissionStage
    formalisationAuthor : TransmissionStage
    downstreamBridge : TransmissionStage
    pathReference : String
    proofAuthorityCreatedByPath : Bool
    empiricalAuthorityCreatedByPath : Bool

open TransmissionPath public

canonicalDiotimaTransmissionPath : TransmissionPath
canonicalDiotimaTransmissionPath =
  transmission-path
    Source.jmdBundleSource
    (transmission-stage "Plato" dialogueAuthorRole quotedOrReconstructedClaim true)
    (transmission-stage "Socrates as dramatic/reporting speaker" dramaticSpeakerRole reportedTeaching true)
    (transmission-stage "Diotima as source-attributed teacher within the dialogue" reportedTeacherRole reportedTeaching true)
    (transmission-stage "James Michael DuPont (JMD / meta-introspector)" formalisationAuthorRole formalisedProposition true)
    (transmission-stage "DASHI structural bridge" dashiBridgeAuthorRole structuralCrossPollination true)
    "source-bounded dialogue -> reported teaching -> JMD Lean formalisation -> DASHI bridge"
    false
    false

------------------------------------------------------------------------
-- Same immediate speaker, different claim role.
------------------------------------------------------------------------

data SpeakerWorld : Set where
  socratesOwnArgumentWorld : SpeakerWorld
  socratesReportsDiotimaWorld : SpeakerWorld

data ImmediateSpeakerSurface : Set where
  socratesSpeakingSurface : ImmediateSpeakerSurface

data ClaimRoleQuery : Set where
  claimRoleQuestion : ClaimRoleQuery

data ClaimRoleAnswer : Set where
  originatingSpeakerClaim : ClaimRoleAnswer
  reportedTeacherClaim : ClaimRoleAnswer

immediateSpeakerProjection : SpeakerWorld → ImmediateSpeakerSurface
immediateSpeakerProjection socratesOwnArgumentWorld = socratesSpeakingSurface
immediateSpeakerProjection socratesReportsDiotimaWorld = socratesSpeakingSurface

ClaimRoleAnswerFor : ClaimRoleQuery → Set
ClaimRoleAnswerFor claimRoleQuestion = ClaimRoleAnswer

askClaimRole : (query : ClaimRoleQuery) → SpeakerWorld → ClaimRoleAnswerFor query
askClaimRole claimRoleQuestion socratesOwnArgumentWorld = originatingSpeakerClaim
askClaimRole claimRoleQuestion socratesReportsDiotimaWorld = reportedTeacherClaim

claimRoleQuestions : Query.InquiryQuestionFamily SpeakerWorld ClaimRoleQuery
claimRoleQuestions = Query.inquiryQuestionFamily ClaimRoleAnswerFor askClaimRole

immediateSpeakerDoesNotDetermineClaimRole :
  Query.FactorsThrough claimRoleQuestions immediateSpeakerProjection claimRoleQuestion → ⊥
immediateSpeakerDoesNotDetermineClaimRole factor = helper first second
  where
    first : originatingSpeakerClaim ≡ Query.quotientAnswer factor socratesSpeakingSurface
    first = Query.factorisation factor socratesOwnArgumentWorld
    second : reportedTeacherClaim ≡ Query.quotientAnswer factor socratesSpeakingSurface
    second = Query.factorisation factor socratesReportsDiotimaWorld
    helper :
      originatingSpeakerClaim ≡ Query.quotientAnswer factor socratesSpeakingSurface →
      reportedTeacherClaim ≡ Query.quotientAnswer factor socratesSpeakingSurface → ⊥
    helper refl ()

------------------------------------------------------------------------
-- Canonical attribution / snowball pins.
------------------------------------------------------------------------

existingJMDBundleSnowballReceipt : Snowball.SourceRoleSnowballReceipt Source.jmdBundleSource
existingJMDBundleSnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt Source.jmdBundleSource

existingAttributionSnowballBoundary : Snowball.AttributionSnowballBoundary
existingAttributionSnowballBoundary = Snowball.canonicalAttributionSnowballBoundary

citationDoesNotCreateProof : Snowball.CitationCreatesProof → ⊥
citationDoesNotCreateProof = Snowball.citationDoesNotCreateProof

citationDoesNotCreateAuthority : Snowball.CitationCreatesDomainAuthority → ⊥
citationDoesNotCreateAuthority = Snowball.citationDoesNotCreateAuthority

sourceKindRetainedAcrossSnowball :
  Snowball.sourceKindRetained existingJMDBundleSnowballReceipt ≡ true
sourceKindRetainedAcrossSnowball = refl

formalisationRelationshipRetainedAcrossSnowball :
  Snowball.formalisationRelationshipRetained existingJMDBundleSnowballReceipt ≡ true
formalisationRelationshipRetainedAcrossSnowball = refl

proofNonImportRetainedAcrossSnowball :
  Snowball.proofNonImportRetained existingJMDBundleSnowballReceipt ≡ true
proofNonImportRetainedAcrossSnowball = refl

authorityNonCreationRetainedAcrossSnowball :
  Snowball.authorityNonCreationRetained existingJMDBundleSnowballReceipt ≡ true
authorityNonCreationRetainedAcrossSnowball = refl

record PlatoSymposiumTransmissionBoundary : Set where
  constructor plato-symposium-transmission-boundary
  field
    immediateSpeakerEqualsReportedSource : Bool
    reportedSourceEqualsDialogueAuthor : Bool
    dialogueAuthorEqualsFormalisationAuthor : Bool
    formalisationAuthorEqualsDASHIBridgeAuthor : Bool
    transmissionPathCreatesHistoricalVerification : Bool
    transmissionPathCreatesProofAuthority : Bool
    JMDAttributionRetained : Bool
    sourceRoleRetainedAcrossSnowball : Bool
    sourceBoundedNarrativeRoleRequired : Bool

open PlatoSymposiumTransmissionBoundary public

canonicalPlatoSymposiumTransmissionBoundary : PlatoSymposiumTransmissionBoundary
canonicalPlatoSymposiumTransmissionBoundary =
  plato-symposium-transmission-boundary false false false false false false true true true

------------------------------------------------------------------------
-- Compatibility surface for the dedicated concurrent regression owner.
------------------------------------------------------------------------

canonicalPlatoTransmissionAttributionBoundary : PlatoSymposiumTransmissionBoundary
canonicalPlatoTransmissionAttributionBoundary = canonicalPlatoSymposiumTransmissionBoundary

immediateSpeakerDeterminesClaimRole : PlatoSymposiumTransmissionBoundary → Bool
immediateSpeakerDeterminesClaimRole _ = false

historicalSpeakerEqualsFormalisationAuthor : PlatoSymposiumTransmissionBoundary → Bool
historicalSpeakerEqualsFormalisationAuthor = dialogueAuthorEqualsFormalisationAuthor

dramaticAttributionCreatesClaimAuthority : PlatoSymposiumTransmissionBoundary → Bool
dramaticAttributionCreatesClaimAuthority = transmissionPathCreatesProofAuthority

layeredTransmissionPathRetained : PlatoSymposiumTransmissionBoundary → Bool
layeredTransmissionPathRetained = sourceRoleRetainedAcrossSnowball

transmissionSummary : String
transmissionSummary =
  "A Symposium proposition may have layered dialogue, dramatic-speaker, reported-source, formalisation-author and downstream-bridge coordinates. The same immediate speaker can carry different claim roles, so attribution must retain transmission role and source lineage; citation or snowball transport creates neither proof nor empirical authority."
