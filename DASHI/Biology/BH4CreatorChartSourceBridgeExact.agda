module DASHI.Biology.BH4CreatorChartSourceBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Biology.KitzerowBH4SourceRegistry as Creator
import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Finite
import DASHI.Biology.BH4PathwayOntologyInteropExact as Ontology
import DASHI.Biology.BH4PathwayReviewInteropExact as Review
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- SOURCE-FIRST BH4 PATHWAY / EXTERNAL DATABASE CORRESPONDENCE
--
-- Kimberly Kitzerow (Jan 2024), "BH4/Folate/Cobalamin/Homocysteine
-- Pathway", ResearchGate record 377218425. Public webpage exposes
-- Rhea codes, enzymes, cofactors, inputs, outputs; creator's original
-- chart layout is copyrighted CC BY-NC-ND 4.0. Source page reports a
-- later displayed full-text upload 2025-08-08. Distinguish these dates.
--
-- Creator-specific network selection, structure and proposed mechanisms
-- remain Kitzerow's work. Rhea independently owns reaction definitions.
-- SensibLaw has a provider-neutral external_graph_bridge / world_model /
-- linkage-adapters architecture; this module claims no second ontology.
-- All actual overlap computation remains an explicitly executed Python
-- comparison of exact observed source IDs with the finite panel.
------------------------------------------------------------------------

publishedOriginalChart : Creator.SourceRecord
publishedOriginalChart = Creator.kitzerow2024BH4FolateChart

observedSourceRheaIds : List String
observedSourceRheaIds =
  "RHEA:10112" ∷
  "RHEA:10580" ∷
  "RHEA:11172" ∷
  "RHEA:19201" ∷
  "RHEA:21080" ∷
  "RHEA:21708" ∷
  "RHEA:23252" ∷
  "RHEA:23908" ∷
  []

observedSourceRheaIdCount : Nat
observedSourceRheaIdCount = 8

observedIndexFinitePanelIdCount : Nat
observedIndexFinitePanelIdCount = Finite.executedPanelReactionCount

observedIndexFinitePanelIdCountExact :
  observedIndexFinitePanelIdCount ≡ 12
observedIndexFinitePanelIdCountExact = refl

record OriginalChartCorrespondenceBoundary : Set where
  constructor original-chart-correspondence-boundary
  field
    creatorSelectedOriginalChartPresent : Bool
    fullCreatorProprietaryNetworkAcquired : Bool
    fullCreatorProprietaryNetworkAcquiredFalse :
      fullCreatorProprietaryNetworkAcquired ≡ false
    originalSourcePDFDigestVerified : Bool
    originalSourcePDFDigestVerifiedFalse :
      originalSourcePDFDigestVerified ≡ false
    publicationDateEqualsDisplayedUploadDate : Bool
    publicationDateEqualsDisplayedUploadDateFalse :
      publicationDateEqualsDisplayedUploadDate ≡ false
    sourceIDMatchesPhysicalSameContextReaction : Bool
    sourceIDMatchesPhysicalSameContextReactionFalse :
      sourceIDMatchesPhysicalSameContextReaction ≡ false
    fullCreatorNetworkCoverageRatioKnown : Bool
    fullCreatorNetworkCoverageRatioKnownFalse :
      fullCreatorNetworkCoverageRatioKnown ≡ false
    chartObservationPaysClinicalMechanism : Bool
    chartObservationPaysClinicalMechanismFalse :
      chartObservationPaysClinicalMechanism ≡ false
    genericExternalOntologyOwnerReused : Bool

canonicalOriginalChartBoundary : OriginalChartCorrespondenceBoundary
canonicalOriginalChartBoundary =
  original-chart-correspondence-boundary true
    false refl false refl false refl false refl false refl false refl
    true

existingOntologyAdapterOwner : Set
existingOntologyAdapterOwner = Ontology.TypedPathwayAssertion

existingReviewAdapterOwner : Set
existingReviewAdapterOwner = Review.SourceReopenablePathwayObligation

canonicalOriginalChartReceipt : Receipt.GenericReceipt
canonicalOriginalChartReceipt =
  Receipt.mkNonPromotingReceipt
    "Kitzerow original Rhea-coded chart / DASHI finite panel"
    "DASHI.Biology.BH4CreatorChartSourceBridgeExact"
    "ResearchGate 377218425; published-page month 2024-01; displayed full-text upload 2025-08-08; public web-text ID locator index"
    "eight bounded source-observed Rhea identifiers; exact intersection and symmetric difference computed against the existing 12-column finite panel, no assumed coverage denominator"
    "original PDF binary and complete proprietary network unverified; ID overlap does not prove same biological context, kinetics, causality or ontology authority"
    "python3 scripts/check_kitzerow_primary_chart.py"
