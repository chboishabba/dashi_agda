module DASHI.Chemistry.LineageAttributionAcquisitionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.LineageAttributionAcquisitionParetoExact as Pareto

------------------------------------------------------------------------
-- CONTACT/EXPOSURE PROVENANCE EXTENSION OVER THE CANONICAL SCIENTIFIC PARETO
--
-- The existing Pareto owner remains authoritative for scientific/calibration
-- acquisition. This module adds only the genuinely orthogonal Kitzerow
-- contact/exposure provenance queue and keeps it separate from scientific
-- support, derivation and plagiarism/legal conclusions.
------------------------------------------------------------------------

data ProvenanceAcquisitionKind : Set where
  contactMessageArtifact : ProvenanceAcquisitionKind
  correspondenceThreadArtifact : ProvenanceAcquisitionKind
  manuscriptHistoryArtifact : ProvenanceAcquisitionKind
  institutionalRoleTimeline : ProvenanceAcquisitionKind

data ProvenanceStatus : Set where
  originatorReportedOnly : ProvenanceStatus
  artifactAcquiredUnverified : ProvenanceStatus
  artifactAuthenticated : ProvenanceStatus
  directUseDocumented : ProvenanceStatus

record ProvenanceAcquisitionItem : Set where
  constructor provenanceAcquisitionItem
  field
    itemKey : String
    kind : ProvenanceAcquisitionKind
    targetAttributionReference : String
    claimedEventReference : String
    exactArtifactNeed : String
    authenticationNeed : String
    expectedUpgrade : String
    currentStatus : ProvenanceStatus
    acquisitionCostRank : Nat
    attributionValueRank : Nat
    causalScientificValueRank : Nat
    truthRank : Nat
    truthRankIsSentinelOnly : Bool
    truthRankIsSentinelOnlyIsTrue : truthRankIsSentinelOnly ≡ true

open ProvenanceAcquisitionItem public

stanfordContactArtifact : ProvenanceAcquisitionItem
stanfordContactArtifact =
  provenanceAcquisitionItem
    "P1 Stanford contact provenance"
    contactMessageArtifact
    "Kitzerow priority/attribution: Stanford"
    "claimed 27 Nov 2023 Stanford Neurodiversity Project contact requesting model information"
    "underlying email/message export with sender, recipient, timestamp and substantive content"
    "message metadata/context sufficient to authenticate communication and chronology"
    "may upgrade originator-reported contact to inspected/authenticated exposure evidence only"
    originatorReportedOnly
    3 10 0 0 true refl

brazilCorrespondenceArtifact : ProvenanceAcquisitionItem
brazilCorrespondenceArtifact =
  provenanceAcquisitionItem
    "P2 Brazil/MDPI correspondence provenance"
    correspondenceThreadArtifact
    "Kitzerow priority/attribution: BH4 systematic review"
    "claimed MDPI/Latini correspondence after attribution concern"
    "underlying correspondence plus manuscript/publication timeline records"
    "message/export authenticity and chronology against manuscript versions"
    "may resolve who communicated what and when; does not by itself establish derivation/copying"
    originatorReportedOnly
    4 10 0 0 true refl

iaccMedMapsContactArtifact : ProvenanceAcquisitionItem
iaccMedMapsContactArtifact =
  provenanceAcquisitionItem
    "P3 IACC/MedMaps contact provenance"
    contactMessageArtifact
    "Kitzerow priority/attribution: IACC developmental-systems framework"
    "claimed 2024 MedMaps/Honey Rinicella awareness/contact before later IACC role"
    "underlying message/export with date, participants and substantive content"
    "communication metadata plus institutional-role chronology"
    "may upgrade awareness/exposure evidence; scientific convergence and derivation remain separate"
    originatorReportedOnly
    4 10 0 0 true refl

canonicalContactProvenanceItems : List ProvenanceAcquisitionItem
canonicalContactProvenanceItems =
  stanfordContactArtifact ∷ brazilCorrespondenceArtifact ∷ iaccMedMapsContactArtifact ∷ []

scientificAcquisitionFrontier : Pareto.LineageAttributionAcquisitionFrontier
scientificAcquisitionFrontier = Pareto.canonicalLineageAttributionAcquisitionFrontier

record UnifiedLineageAttributionAcquisitionFrontier : Set where
  constructor unifiedLineageAttributionAcquisitionFrontier
  field
    scientificFrontier : Pareto.LineageAttributionAcquisitionFrontier
    contactProvenanceItems : List ProvenanceAcquisitionItem
    canonicalScientificParetoReused : Bool
    canonicalScientificParetoReusedIsTrue : canonicalScientificParetoReused ≡ true
    scientificSupportSeparateFromContactProvenance : Bool
    scientificSupportSeparateFromContactProvenanceIsTrue :
      scientificSupportSeparateFromContactProvenance ≡ true
    contactEvidenceAutomaticallyProvesDerivation : Bool
    contactEvidenceAutomaticallyProvesDerivationIsFalse :
      contactEvidenceAutomaticallyProvesDerivation ≡ false
    contactEvidenceAutomaticallyProvesPlagiarism : Bool
    contactEvidenceAutomaticallyProvesPlagiarismIsFalse :
      contactEvidenceAutomaticallyProvesPlagiarism ≡ false
    scientificSupportAutomaticallyProvesPriority : Bool
    scientificSupportAutomaticallyProvesPriorityIsFalse :
      scientificSupportAutomaticallyProvesPriority ≡ false
    frontierRankIsTruthRank : Bool
    frontierRankIsTruthRankIsFalse : frontierRankIsTruthRank ≡ false
    unpaidCoordinateRetainsAttribution : Bool
    unpaidCoordinateRetainsAttributionIsTrue : unpaidCoordinateRetainsAttribution ≡ true

open UnifiedLineageAttributionAcquisitionFrontier public

canonicalLineageAttributionAcquisitionFrontier : UnifiedLineageAttributionAcquisitionFrontier
canonicalLineageAttributionAcquisitionFrontier =
  unifiedLineageAttributionAcquisitionFrontier
    scientificAcquisitionFrontier
    canonicalContactProvenanceItems
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
