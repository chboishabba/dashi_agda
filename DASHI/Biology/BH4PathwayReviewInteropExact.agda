module DASHI.Biology.BH4PathwayReviewInteropExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4PathwayOntologyInteropExact as Pathway
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
import DASHI.Ontology.WikidataRepairReopeningExact as Reopen
import DASHI.Ontology.WikidataConsumerResidualRefinementExact as Residual
import DASHI.Wikimedia.WikidataOntologyDiagnosticS29BridgeExact as S29
import DASHI.Interop.ReadingTrailPNFProgressiveDisclosureExact as Reading
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- KITZEROW BH4 PATHWAY REVIEW WORKLIST / CROSS-PRODUCT USER STORIES
--
-- Reuses ITIR-suite/docs/user_stories.md:
--   ITIR-US-01, ITIR-US-02, ITIR-US-17;
--   WIKI-US-01..04 / SL-US-38..41.
-- Reuses existing Wikidata candidate-only repair (Vrandečić and Krötzsch,
-- "Wikidata: a free collaborative knowledgebase", CACM 57(10), 2014,
-- DOI 10.1145/2629489) and DASHI PNF reopening.
--
-- Kitzerow proposed model: 2024-01 DOI 10.13140/RG.2.2.23124.37761/1
-- and 2024-08 ResearchGate publication 383021907.
-- This review projection is DASHI-authored. It is not an SLR PostgreSQL
-- S29 receipt, a verified author transcription or ontology edit authority.
------------------------------------------------------------------------

data PathwayDiagnosticOrigin : Set where
  missingPrimaryPassage : PathwayDiagnosticOrigin
  reactionCompartmentUnpaid : PathwayDiagnosticOrigin
  speciesCompartmentUnpaid : PathwayDiagnosticOrigin
  reactionMagnitudeUnpaid : PathwayDiagnosticOrigin
  reactionDirectionUnpaid : PathwayDiagnosticOrigin
  exchangeMagnitudeUnpaid : PathwayDiagnosticOrigin
  mappingSemanticsUnpaid : PathwayDiagnosticOrigin
  sourceAnnotationUnparsed : PathwayDiagnosticOrigin
  nonfiniteChemistryUnresolved : PathwayDiagnosticOrigin

data PathwayReviewAuthority : Set where
  readOnlyCandidate : PathwayReviewAuthority

data PathwayEditPermission : PathwayReviewAuthority → Set where
data PathwayTruthPermission : PathwayReviewAuthority → Set where

candidateCannotEditWiki :
  PathwayEditPermission readOnlyCandidate → ⊥
candidateCannotEditWiki ()

candidateCannotAssertTruth :
  PathwayTruthPermission readOnlyCandidate → ⊥
candidateCannotAssertTruth ()

record SourceReopenablePathwayObligation : Set where
  constructor source-reopenable-pathway-obligation
  field
    obligationRef : String
    ownerCoordinate : String
    diagnosticOrigin : PathwayDiagnosticOrigin
    sourceRevisionRef : String
    sourceSpanOrReceiptRef : String
    proofDemand : String
    proposedAction : Repair.RepairOperation
    viewDepth : Reading.DisclosureDepth
    reviewAuthority : PathwayReviewAuthority

open SourceReopenablePathwayObligation public

candidateAuthorPassage : SourceReopenablePathwayObligation
candidateAuthorPassage =
  source-reopenable-pathway-obligation
    "KPO-01"
    "SRC-KIT-2024-08"
    missingPrimaryPassage
    "ResearchGate publication 383021907; version pin needed"
    "KitzerowBH4SystemNongNangMaxCutExact; original passage pin missing"
    "exact author statement, passage, author/date and scope"
    Repair.holdForReview
    Reading.sourceDepth
    readOnlyCandidate

candidateDirection : SourceReopenablePathwayObligation
candidateDirection =
  source-reopenable-pathway-obligation
    "KPO-06"
    "RHEA:19897"
    reactionDirectionUnpaid
    "Rhea release 142 (2026-09-02); SPARQL release 2026_03"
    "BH4PanelStoichiometricMatrixExact; source receipt for NOS reaction"
    "same isoform, compartment, substrate and thermodynamic context"
    Repair.holdForReview
    Reading.proofConeDepth
    readOnlyCandidate

record PathwayReviewFirewall : Set where
  constructor pathway-review-firewall
  field
    sourceLocatorAutomaticallyVerifiesHistoricalDocument : Bool
    sourceLocatorAutomaticallyVerifiesHistoricalDocumentIsFalse :
      sourceLocatorAutomaticallyVerifiesHistoricalDocument ≡ false
    ontologyJoinProvesSameBiologicalProcess : Bool
    ontologyJoinProvesSameBiologicalProcessIsFalse :
      ontologyJoinProvesSameBiologicalProcess ≡ false
    diagnosticRepairGrantsPublicEdit : Bool
    diagnosticRepairGrantsPublicEditIsFalse :
      diagnosticRepairGrantsPublicEdit ≡ false
    reviewerStatusCreatesMedicalTruth : Bool
    reviewerStatusCreatesMedicalTruthIsFalse :
      reviewerStatusCreatesMedicalTruth ≡ false
    missingFluxBecomesMeasuredZero : Bool
    missingFluxBecomesMeasuredZeroIsFalse :
      missingFluxBecomesMeasuredZero ≡ false

canonicalPathwayReviewFirewall : PathwayReviewFirewall
canonicalPathwayReviewFirewall =
  pathway-review-firewall false refl false refl false refl false refl false refl

-- Depend on existing owners, not a substitute pathway-specific ontology.
pathwayAssertionOwner : Set
pathwayAssertionOwner = Pathway.TypedPathwayAssertion

existingRepairOperation : Set
existingRepairOperation = Repair.RepairOperation

existingS29DiagnosticOwner : Set
existingS29DiagnosticOwner = S29.DiagnosticDisposition

-- The Wikidata theorem is only a reusable *pattern*: its original finite
-- counterexample is not automatically an empirical BH4 theorem.
existingResidualOriginOwner : Set
existingResidualOriginOwner = Residual.WikidataConsumerResidualRefinementBoundary

existingReopeningCarrier : Set
existingReopeningCarrier = Reopen.RepairCandidate

canonicalPathwayReviewReceipt : Receipt.GenericReceipt
canonicalPathwayReviewReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 pathway source review and residual worklist"
    "DASHI.Biology.BH4PathwayReviewInteropExact"
    "canonical BH4 typed graph plus existing Wikidata repair/reopening/PNF and ReadingTrail owners"
    "classifies source, mapping, compartment, flux and chemical representation gaps as read-only, source-reopenable review obligations"
    "cross-source adjacency, caller hashes and review status grant no ontology edit, physiological causality, exact historical source authentication, S29 persistence or medical promotion"
    "python3 scripts/check_bh4_pathway_review.py"
