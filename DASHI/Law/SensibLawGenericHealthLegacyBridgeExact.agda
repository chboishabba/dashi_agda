module DASHI.Law.SensibLawGenericHealthLegacyBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawHealthRecordEvidenceExact as Generic
import DASHI.Law.SensibLawLaterMedicalParticularHarmSourceConditionedExact as Legacy

------------------------------------------------------------------------
-- GENERIC HEALTH ALGEBRA <-> EXISTING LATER-MEDICAL OWNER
--
-- The generic health algebra is a promotion of common structure, not a second
-- competing ontology.  Existing later-medical fixtures may be related to it
-- only through explicit same-carrier / same-proposition receipts.
------------------------------------------------------------------------

record GenericLaterMedicalBridge : Set₁ where
  constructor genericLaterMedicalBridge
  field
    genericArtifact : Generic.HealthRecordArtifact
    genericAtom : Generic.HealthAtom
    legacyEvidence : Legacy.LaterMedicalEvidence
    legacyAtom : Legacy.SourceConditionedHarmAtom
    sameCarrierReceipt : Set
    samePropositionReceipt : Set
    bridgeReference : String

open GenericLaterMedicalBridge public

record GenericLegacyParticularHarmBridge : Set₁ where
  constructor genericLegacyParticularHarmBridge
  field
    genericWeld : Generic.ParticularHarmIdentityWeld
    legacyWeld : Legacy.ParticularHarmIdentityWeld
    samePleadedHarmReceipt : Set
    sameClinicalHarmReceipt : Set
    bridgeReference : String

open GenericLegacyParticularHarmBridge public

record GenericHealthLegacyBoundary : Set where
  constructor genericHealthLegacyBoundary
  field
    genericLayerReplacesLegacyOwner : Bool
    genericLayerReplacesLegacyOwnerIsFalse :
      genericLayerReplacesLegacyOwner ≡ false
    matchingCarrierNamesEstablishSameCarrier : Bool
    matchingCarrierNamesEstablishSameCarrierIsFalse :
      matchingCarrierNamesEstablishSameCarrier ≡ false
    matchingPropositionTextEstablishesSameProposition : Bool
    matchingPropositionTextEstablishesSamePropositionIsFalse :
      matchingPropositionTextEstablishesSameProposition ≡ false
    explicitBridgeReceiptsRequired : Bool
    explicitBridgeReceiptsRequiredIsTrue :
      explicitBridgeReceiptsRequired ≡ true

canonicalGenericHealthLegacyBoundary : GenericHealthLegacyBoundary
canonicalGenericHealthLegacyBoundary =
  genericHealthLegacyBoundary
    false refl
    false refl
    false refl
    true refl

data GenericLayerAutomaticallyReplacesLegacyOwner : Set where
data MatchingCarrierNameAutomaticallySameCarrier : Set where
data MatchingPropositionAutomaticallySameProposition : Set where

genericLayerDoesNotReplaceLegacyOwner :
  GenericLayerAutomaticallyReplacesLegacyOwner → ⊥
genericLayerDoesNotReplaceLegacyOwner ()

matchingCarrierNameDoesNotAutoIdentifyCarrier :
  MatchingCarrierNameAutomaticallySameCarrier → ⊥
matchingCarrierNameDoesNotAutoIdentifyCarrier ()

matchingPropositionDoesNotAutoIdentifyProposition :
  MatchingPropositionAutomaticallySameProposition → ⊥
matchingPropositionDoesNotAutoIdentifyProposition ()
