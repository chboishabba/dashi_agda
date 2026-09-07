module DASHI.Physics.GR.GravitationalEpistemicLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.GR.GravitationalObservationSourceAtlasExact as Sources

------------------------------------------------------------------------
-- CARRIER-SENSITIVE ATTRIBUTION FOR GRAVITY / OBSERVATION WORK
--
-- External source claims, DASHI reconstruction/inference, and internal theorem
-- lineage are intentionally different carriers.  No artifact promotes itself.
------------------------------------------------------------------------

data EpistemicLayer : Set where
  externalObservationClaim : EpistemicLayer
  externalTheoryClaim : EpistemicLayer
  dashiReconstruction : EpistemicLayer
  dashiDerivedComparison : EpistemicLayer
  internalTheoremLineage : EpistemicLayer

data ScientificStableIdentifierKind : Set where
  doiIdentifier : ScientificStableIdentifierKind
  arxivIdentifier : ScientificStableIdentifierKind
  officialStableURLIdentifier : ScientificStableIdentifierKind
  repositoryRevisionIdentifier : ScientificStableIdentifierKind

record ExternalTheoryAttributedSource : Set where
  constructor external-theory-attributed-source
  field
    authorOrResponsibleBody : String
    title : String
    stableIdentifierKind : ScientificStableIdentifierKind
    stableIdentifier : String
    carrierURL : String
    inspectedOn : String
    exactSourceEntitledClaim : String
    inspectedForExactClaim : Bool

open ExternalTheoryAttributedSource public

record ExternalObservationClaimLineage : Set where
  constructor external-observation-claim-lineage
  field
    source : Sources.ObservationAttributedSource
    boundedClaim : String
    layer : EpistemicLayer
    layerIsExternalObservation : layer ≡ externalObservationClaim

open ExternalObservationClaimLineage public

record DASHIReconstructionLineage : Set where
  constructor dashi-reconstruction-lineage
  field
    upstreamObservationSources : List Sources.ObservationAttributedSource
    reconstructionCarrier : String
    reconstructionRevision : String
    reconstructionStatement : String
    layer : EpistemicLayer
    layerIsDASHIReconstruction : layer ≡ dashiReconstruction
    representedAsExternalSourceClaim : Bool

open DASHIReconstructionLineage public

record DASHIDerivedComparisonLineage : Set where
  constructor dashi-derived-comparison-lineage
  field
    upstreamObservationSources : List Sources.ObservationAttributedSource
    comparisonCarrier : String
    comparisonRevision : String
    derivedStatement : String
    layer : EpistemicLayer
    layerIsDASHIDerivedComparison : layer ≡ dashiDerivedComparison
    representedAsExternalSourceClaim : Bool

open DASHIDerivedComparisonLineage public

record InternalTheoremProofLineage : Set where
  constructor internal-theorem-proof-lineage
  field
    modulePath : String
    theoremName : String
    repositoryRevision : String
    proofStatementScope : String
    layer : EpistemicLayer
    layerIsInternalTheorem : layer ≡ internalTheoremLineage
    freshExternalBibliographyRequired : Bool

open InternalTheoremProofLineage public

------------------------------------------------------------------------
-- Canonical firewalls.
------------------------------------------------------------------------

record GravitationalEpistemicLineageBoundary : Set where
  constructor gravitational-epistemic-lineage-boundary
  field
    externalScientificClaimRequiresAuthorTitleStableIdentifier : Bool
    missingMetadataMayBeInvented : Bool
    sourceEntitledClaimEqualsDASHIReconstruction : Bool
    dashiReconstructionEqualsDerivedComparison : Bool
    sourceCitationAutomaticallyPaysPhysicalClaim : Bool
    internalTheoremRequiresFreshExternalBibliography : Bool
    internalTheoremProvesMoreThanEncodedStatement : Bool
    attributionMustSurviveObservationPredictionResidualBridges : Bool

canonicalGravitationalEpistemicLineageBoundary : GravitationalEpistemicLineageBoundary
canonicalGravitationalEpistemicLineageBoundary =
  gravitational-epistemic-lineage-boundary
    true false false false false false false true

------------------------------------------------------------------------
-- A local theorem carrier uses proof lineage rather than fake publication
-- metadata.  This fixture pins the carrier-sensitive policy explicitly.
------------------------------------------------------------------------

predictionObservationWeldProofLineage : InternalTheoremProofLineage
predictionObservationWeldProofLineage =
  internal-theorem-proof-lineage
    "DASHI/Physics/GR/GravitationalPredictionObservationBidiExact.agda"
    "PredictionObservationWeld"
    "agent/antigravity-material-bidi-xpoll"
    "typed same-channel and same-observable comparison carrier only"
    internalTheoremLineage refl false
