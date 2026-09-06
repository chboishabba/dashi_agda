module DASHI.Economics.SourceAttributionPromotionBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION / PROMOTION BOUNDARY
--
-- Reuses the source-attribution discipline established elsewhere in DASHI:
--
--   source proposition
--   != later interpretation
--   != DASHI reconstruction
--   != DASHI theorem
--   != empirical/systemic conclusion.
--
-- Access location, publication carrier, speaker/claim owner, formalisation
-- owner and promotion authority are kept as separate coordinates.  A mirror,
-- transcript, news report or jointly published document cannot manufacture
-- authorship or stronger theorem authority.
------------------------------------------------------------------------

data AttributionLayer : Set where
  primarySourceProposition
  secondarySourceReport
  transcriptProposition
  dashiBoundedInterpretation
  dashiFormalConstruction
  dashiTheorem
  empiricalPromotion
  systemicClassification
  : AttributionLayer

data AccessCarrierRole : Set where
  canonicalCarrier
  primaryCarrierMirror
  secondaryReportingCarrier
  transcriptCarrier
  accessMirrorOnly
  userSuppliedCarrier
  : AccessCarrierRole

record SourceAttributionReceipt : Set where
  constructor sourceAttributionReceipt
  field
    upstreamAuthors : String
    speakerOrClaimOwner : String
    publicationCarrier : String
    canonicalPublicationLocation : String
    accessLocation : String
    accessCarrierRole : AccessCarrierRole
    exactSourceLocation : String
    boundedProposition : String
    attributionLayer : AttributionLayer
    formalisationOwner : String
    promotionAuthority : String
    primarySourceRecovered : Bool
    claimOwnerRecovered : Bool
    exactLocationRecovered : Bool

open SourceAttributionReceipt public

record SourceUseReceipt : Set where
  constructor sourceUseReceipt
  field
    sourceReceipt : SourceAttributionReceipt
    downstreamLayer : AttributionLayer
    preservesSpeakerOwnership : Bool
    preservesSourceLocation : Bool
    preservesCarrierRole : Bool
    doesNotPromoteBeyondAuthority : Bool

open SourceUseReceipt public

record IndependentVerificationReceipt : Set where
  constructor independentVerificationReceipt
  field
    transcriptOrSecondaryReceipt : SourceAttributionReceipt
    independentReceipt : SourceAttributionReceipt
    sameBoundedProposition : Bool
    independentProducerEstablished : Bool

open IndependentVerificationReceipt public

------------------------------------------------------------------------
-- Firewalls from previous attribution rounds.
------------------------------------------------------------------------

data AccessCarrierImpliesAuthorshipPermission : Set where

data JointPublicationImpliesEverySentenceJointlyOwnedPermission : Set where

data SourceArgumentImpliesDASHIFormalisationOwnershipPermission : Set where

data SecondaryReportImpliesPrimarySourceAuthorityPermission : Set where

data TranscriptImpliesIndependentVerificationPermission : Set where

data SourcePropositionImpliesSystemicClassificationPermission : Set where

data SameContentImpliesIndependentProducerPermission : Set where

accessCarrierDoesNotAutoPromoteToAuthorship :
  AccessCarrierImpliesAuthorshipPermission → ⊥
accessCarrierDoesNotAutoPromoteToAuthorship ()

jointPublicationDoesNotAutoPromoteEverySentenceToJointOwnership :
  JointPublicationImpliesEverySentenceJointlyOwnedPermission → ⊥
jointPublicationDoesNotAutoPromoteEverySentenceToJointOwnership ()

sourceArgumentDoesNotAutoPromoteToDASHIFormalisationOwnership :
  SourceArgumentImpliesDASHIFormalisationOwnershipPermission → ⊥
sourceArgumentDoesNotAutoPromoteToDASHIFormalisationOwnership ()

secondaryReportDoesNotAutoPromoteToPrimaryAuthority :
  SecondaryReportImpliesPrimarySourceAuthorityPermission → ⊥
secondaryReportDoesNotAutoPromoteToPrimaryAuthority ()

transcriptDoesNotAutoPromoteToIndependentVerification :
  TranscriptImpliesIndependentVerificationPermission → ⊥
transcriptDoesNotAutoPromoteToIndependentVerification ()

sourcePropositionDoesNotAutoPromoteToSystemicClassification :
  SourcePropositionImpliesSystemicClassificationPermission → ⊥
sourcePropositionDoesNotAutoPromoteToSystemicClassification ()

sameContentDoesNotAutoPromoteToIndependentProducer :
  SameContentImpliesIndependentProducerPermission → ⊥
sameContentDoesNotAutoPromoteToIndependentProducer ()
