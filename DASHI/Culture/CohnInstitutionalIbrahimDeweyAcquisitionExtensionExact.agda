module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalExact as Traversal
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim

------------------------------------------------------------------------
-- IBRAHIM / DEWEY ACQUISITION EXTENSION
--
-- Append-only source acquisition over the existing Cohn institutional
-- traversal.  These sources add distinct candidate coordinate families:
--
--   Longino : contextual/social structure of evidential relevance and critique
--   Dotson  : testimony uptake / silencing failure
--   Medina  : plural/polyphonic interpretive resources and shared responsibility
--
-- They are primary conceptual sources for those bounded propositions only.
-- They do not author DASHI's finite collisions, automatic repair diagnosis,
-- legal conclusions, least-coordinate minimality, Pareto costs, or reopening
-- theorems.
------------------------------------------------------------------------

longinoScienceAsSocialKnowledge : Source.AttributedSource
longinoScienceAsSocialKnowledge = Source.mkDOISource
  "Helen E. Longino"
  "Science as Social Knowledge: Values and Objectivity in Scientific Inquiry"
  "Princeton University Press"
  "1990"
  "10.2307/j.ctvx5wbfz"
  "https://doi.org/10.2307/j.ctvx5wbfz"
  Source.academicBookSource
  "Primary conceptual source for contextual evidential relevance, criticism, values and the social conditions of scientific objectivity. It motivates retaining evidential-context and criticism coordinates; it does not prove DASHI consumer adequacy or repair minimality."
  Source.publicAttribution

dotsonTrackingEpistemicViolence : Source.AttributedSource
dotsonTrackingEpistemicViolence = Source.mkDOISource
  "Kristie Dotson"
  "Tracking Epistemic Violence, Tracking Practices of Silencing"
  "Hypatia 26(2), 236-257"
  "2011"
  "10.1111/j.1527-2001.2011.01177.x"
  "https://doi.org/10.1111/j.1527-2001.2011.01177.x"
  Source.academicArticleSource
  "Primary conceptual source for testimony-related silencing and hearer failures in linguistic exchange. It motivates treating testimony uptake and speaker/hearer dependence as potentially missing institutional coordinates; it does not prove any particular institution silenced any particular speaker."
  Source.publicAttribution

medinaPolyphonicContextualism : Source.AttributedSource
medinaPolyphonicContextualism = Source.mkDOISource
  "José Medina"
  "Hermeneutical Injustice and Polyphonic Contextualism: Social Silences and Shared Hermeneutical Responsibilities"
  "Social Epistemology 26(2), 201-220"
  "2012"
  "10.1080/02691728.2011.652214"
  "https://doi.org/10.1080/02691728.2011.652214"
  Source.academicArticleSource
  "Primary conceptual source for relational/polyphonic contextualism, social silences and shared hermeneutical responsibility. It motivates checking plural interpretive-resource coordinates; it does not author DASHI's finite observer or repair constructions."
  Source.publicAttribution

acquisitionExtensionAtlas : Source.AttributedSourceAtlas
acquisitionExtensionAtlas = Source.mkSourceAtlas
  "Cohn institutional Ibrahim/Dewey acquisition extension"
  "DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionExact"
  (longinoScienceAsSocialKnowledge ∷
   dotsonTrackingEpistemicViolence ∷
   medinaPolyphonicContextualism ∷ [])
  "Append-only primary-source extension for evidential context, testimony uptake/silencing, and plural interpretive resources. Source identity and conceptual relevance remain distinct from DASHI theorem ownership, historical influence, legal authority and case-specific factual findings."

------------------------------------------------------------------------
-- Identifier state.
--
-- Only Helen Longino's author QID was positively verified in this pass.
-- Publication-item QIDs for all three works, and person-QIDs for Dotson and the
-- intended philosopher José Medina, remain unresolved rather than guessing or
-- accepting ambiguous same-name entities.
------------------------------------------------------------------------

helenLonginoAuthorQid : Id.ItemId
helenLonginoAuthorQid = Id.itemId "Q5702699"

longinoPublicationIdentity : Traversal.ItemResolution
longinoPublicationIdentity = Traversal.unresolvedItem
  "publication-item QID for Science as Social Knowledge not verified in this acquisition pass; Helen Longino author Q5702699 is retained separately"

dotsonPublicationIdentity : Traversal.ItemResolution
dotsonPublicationIdentity = Traversal.unresolvedItem
  "publication-item QID for Tracking Epistemic Violence not verified in this acquisition pass; no person-QID is asserted for Kristie Dotson here"

medinaPublicationIdentity : Traversal.ItemResolution
medinaPublicationIdentity = Traversal.unresolvedItem
  "publication-item QID for Hermeneutical Injustice and Polyphonic Contextualism not verified in this acquisition pass; ambiguous José Medina QIDs are not promoted to the philosopher"

record AcquisitionIdentifierBoundary : Set where
  constructor acquisitionIdentifierBoundary
  field
    longinoAuthorQidResolved : Bool
    longinoPublicationQidResolved : Bool
    dotsonPublicationQidResolved : Bool
    medinaPublicationQidResolved : Bool
    unresolvedPersonNameMayBorrowSameNameQid : Bool
    authorQidMaySubstituteForPublicationQid : Bool

open AcquisitionIdentifierBoundary public

canonicalAcquisitionIdentifierBoundary : AcquisitionIdentifierBoundary
canonicalAcquisitionIdentifierBoundary =
  acquisitionIdentifierBoundary true false false false false false

------------------------------------------------------------------------
-- Dewey navigation coordinates.
-- Broad parents only; no claim of publication-specific catalogue assignment.
------------------------------------------------------------------------

philosophyOfScienceDewey : String
philosophyOfScienceDewey = "501.000"

socialEpistemologyDewey : String
socialEpistemologyDewey = "121.000"

------------------------------------------------------------------------
-- Source coordinates.
------------------------------------------------------------------------

longinoEvidenceContextCoordinate : Ibrahim.DashiKnowledgeCoordinate
longinoEvidenceContextCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "contextual evidential relevance / social criticism conditions"
  philosophyOfScienceDewey
  "publication QID unresolved; Helen Longino author Q5702699 retained separately"
  "doi:10.2307/j.ctvx5wbfz"

dotsonTestimonyUptakeCoordinate : Ibrahim.DashiKnowledgeCoordinate
dotsonTestimonyUptakeCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "testimony uptake / practices of silencing"
  socialEpistemologyDewey
  "publication QID unresolved"
  "doi:10.1111/j.1527-2001.2011.01177.x"

medinaInterpretiveResourcesCoordinate : Ibrahim.DashiKnowledgeCoordinate
medinaInterpretiveResourcesCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "polyphonic contextualism / shared hermeneutical responsibility"
  socialEpistemologyDewey
  "publication QID unresolved; philosopher person-QID unresolved"
  "doi:10.1080/02691728.2011.652214"

------------------------------------------------------------------------
-- Typed traversal edges into the existing institutional repair frontier.
--
-- These edges mean: when diagnosing a downstream collision, inspect whether
-- this source-bounded coordinate family is relevant. They do not assert that
-- the source uniquely determines the missing coordinate or the repair.
------------------------------------------------------------------------

longinoToEvidenceContext : Ibrahim.DashiFirstLinkEdge
longinoToEvidenceContext = Ibrahim.dashi-first-link-edge
  longinoEvidenceContextCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Longino's contextual account makes evidential relevance and criticism conditions a candidate coordinate family when a consumer collision survives a coarse evidence label. DASHI still has to construct the collision and prove any repair."
  true

dotsonToTestimonyUptake : Ibrahim.DashiFirstLinkEdge
dotsonToTestimonyUptake = Ibrahim.dashi-first-link-edge
  dotsonTestimonyUptakeCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Dotson's analysis makes testimony uptake / hearer-side failure a candidate coordinate family when a consumer depends on whether testimony can enter the institutional surface. No case-specific silencing inference is imported."
  true

medinaToInterpretiveResources : Ibrahim.DashiFirstLinkEdge
medinaToInterpretiveResources = Ibrahim.dashi-first-link-edge
  medinaInterpretiveResourcesCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Medina's polyphonic contextualism makes plurality of interpretive resources and shared hermeneutical responsibility a candidate coordinate family. DASHI independently decides whether such coordinates distinguish a concrete collision."
  true

------------------------------------------------------------------------
-- Acquisition status / attribution firewall.
------------------------------------------------------------------------

record AcquisitionAttributionBoundary : Set where
  constructor acquisitionAttributionBoundary
  field
    contextualEvidenceMeansAnythingGoes : Bool
    silencingSourceProvesSpecificInstitutionalOutcome : Bool
    pluralInterpretiveResourcesCreateAutomaticAdequacy : Bool
    acquiredPrimarySourcesOwnDashiRepairTheorem : Bool
    traversalEdgeCreatesHistoricalInfluence : Bool
    unresolvedQidCreatesNegativeKnowledge : Bool
    acquisitionAddsCandidateCoordinateFamilies : Bool

open AcquisitionAttributionBoundary public

canonicalAcquisitionAttributionBoundary : AcquisitionAttributionBoundary
canonicalAcquisitionAttributionBoundary =
  acquisitionAttributionBoundary
    false false false false false false true

longinoCitationDoesNotImportProof :
  Source.citationImportsProof longinoScienceAsSocialKnowledge ≡ false
longinoCitationDoesNotImportProof = refl

dotsonCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority dotsonTrackingEpistemicViolence ≡ false
dotsonCitationDoesNotCreateAuthority = refl

medinaCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority medinaPolyphonicContextualism ≡ false
medinaCitationDoesNotCreateAuthority = refl

------------------------------------------------------------------------
-- Updated acquisition frontier.
------------------------------------------------------------------------

record AcquisitionFrontier : Set where
  constructor acquisitionFrontier
  field
    acquiredCoordinateFamilies : String
    nextProofUse : String
    qidDebt : String
    deweyDebt : String
    stopRule : String

open AcquisitionFrontier public

canonicalAcquisitionFrontier : AcquisitionFrontier
canonicalAcquisitionFrontier = acquisitionFrontier
  "evidential-context/criticism conditions; testimony uptake/silencing; plural interpretive resources/shared hermeneutical responsibility"
  "test these acquired coordinate families against concrete institutional consumer collisions; promote only a coordinate that actually distinguishes an unpaid fibre"
  "publication QIDs for Longino 1990, Dotson 2011 and Medina 2012 remain unresolved; Dotson and philosopher-Medina person QIDs also remain unresolved rather than using ambiguous name matches"
  "broad 501/121 parents are traversal coordinates only; publication-specific DDC remains unresolved"
  "continue source snowball only when it adds a distinct candidate coordinate family, source identity/provenance payment, or an empirically required premise; semantic adjacency alone is not enough"
