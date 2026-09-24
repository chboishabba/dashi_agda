module DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.CohnTechnostrategicSourceAtlasExact as Cohn
import DASHI.Culture.CohnInstitutionalLeastCoordinateRepairExact as Repair
import DASHI.Ontology.DeweyQidCoverageQualityExact as Coverage
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim

------------------------------------------------------------------------
-- COHN / INSTITUTIONAL IBRAHIM-DEWEY TRAVERSAL
--
-- Thin application of the canonical DASHI traversal and attribution surfaces.
--
-- Separation discipline:
--   * DOI = bibliographic/source-object identity;
--   * publication QID = external publication-item identity when verified;
--   * author QID = author identity only;
--   * concept QID = concept identity only;
--   * Dewey = broad subject-space navigation coordinate;
--   * typed edge = DASHI-selected dependency/cross-pollination relation;
--   * none of the above imports proof or creates authority.
--
-- Broad Dewey parents below are repository navigation coordinates, NOT claims
-- that the exact publication/edition has a verified catalogue assignment to
-- that number. Where publication-QID coverage was not verified in the current
-- traversal, debt remains explicit rather than borrowing an author/concept QID.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- External attributed primary sources newly added by this traversal.
------------------------------------------------------------------------

harawaySituatedKnowledges : Source.AttributedSource
harawaySituatedKnowledges = Source.mkDOISource
  "Donna Haraway"
  "Situated Knowledges: The Science Question in Feminism and the Privilege of Partial Perspective"
  "Feminist Studies 14(3), 575-599"
  "1988"
  "10.2307/3178066"
  "https://doi.org/10.2307/3178066"
  Source.academicArticleSource
  "Primary conceptual source for situated/partial-perspective epistemology. It motivates questions about observer position and responsibility; it does not author DASHI query-indexed factorisation, least-coordinate repair, legal conclusions, or operational authority."
  Source.publicAttribution

blackwellEquivalentComparisons : Source.AttributedSource
blackwellEquivalentComparisons = Source.mkDOISource
  "David Blackwell"
  "Equivalent Comparisons of Experiments"
  "The Annals of Mathematical Statistics 24(2), 265-272"
  "1953"
  "10.1214/aoms/1177729032"
  "https://doi.org/10.1214/aoms/1177729032"
  Source.academicArticleSource
  "Primary statistical decision-theory source for comparison of experiments relative to decision problems. It is conceptual precedent for consumer-relative information comparison only; DASHI owns its finite coordinate-repair candidate family, synthetic costs, minimality proof, and reopening graph."
  Source.publicAttribution

frickerEpistemicInjustice : Source.AttributedSource
frickerEpistemicInjustice = Source.mkDOISource
  "Miranda Fricker"
  "Epistemic Injustice: Power and the Ethics of Knowing"
  "Oxford University Press"
  "2007"
  "10.1093/acprof:oso/9780198237907.001.0001"
  "https://doi.org/10.1093/acprof:oso/9780198237907.001.0001"
  Source.academicBookSource
  "Primary conceptual source for epistemic injustice and power-sensitive failures of knowing. It may motivate institutional-epistemic questions but does not itself establish the repository's finite collisions, legal reasonableness, source genealogy, or least-coordinate repair theorem."
  Source.publicAttribution

institutionalTraversalSourceAtlas : Source.AttributedSourceAtlas
institutionalTraversalSourceAtlas = Source.mkSourceAtlas
  "Cohn institutional Ibrahim/Dewey primary-source traversal atlas"
  "DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalExact"
  (Cohn.cohnSexAndDeath ∷
   harawaySituatedKnowledges ∷
   blackwellEquivalentComparisons ∷
   frickerEpistemicInjustice ∷ [])
  "Primary-source objects reached from the Cohn/institutional consumer-adequacy lane. Traversal proximity records where to inspect next; it does not establish historical identity, agreement, causal continuity, proof authority, legal authority, or universal relevance."

------------------------------------------------------------------------
-- Identifier states. Publication identity, author identity and concept identity
-- never substitute for one another.
------------------------------------------------------------------------

data ItemResolution : Set where
  resolvedItem : Id.ItemId → ItemResolution
  unresolvedItem : String → ItemResolution

cohnSexAndDeathPublicationQid : Id.ItemId
cohnSexAndDeathPublicationQid = Id.itemId "Q104206590"

harawaySituatedKnowledgesPublicationQid : Id.ItemId
harawaySituatedKnowledgesPublicationQid = Id.itemId "Q29014379"

donnaHarawayAuthorQid : Id.ItemId
donnaHarawayAuthorQid = Id.itemId "Q253407"

davidBlackwellAuthorQid : Id.ItemId
davidBlackwellAuthorQid = Id.itemId "Q525037"

mirandaFrickerAuthorQid : Id.ItemId
mirandaFrickerAuthorQid = Id.itemId "Q13522475"

epistemicInjusticeConceptQid : Id.ItemId
epistemicInjusticeConceptQid = Id.itemId "Q48970669"

cohnPublicationIdentity : ItemResolution
cohnPublicationIdentity = resolvedItem cohnSexAndDeathPublicationQid

harawayPublicationIdentity : ItemResolution
harawayPublicationIdentity = resolvedItem harawaySituatedKnowledgesPublicationQid

blackwellPublicationIdentity : ItemResolution
blackwellPublicationIdentity = unresolvedItem
  "publication-item QID not verified in this traversal; David Blackwell author QID Q525037 is retained separately and must not substitute for the article"

frickerPublicationIdentity : ItemResolution
frickerPublicationIdentity = unresolvedItem
  "publication-item QID for the 2007 book not verified in this traversal; Miranda Fricker Q13522475 and epistemic-injustice concept Q48970669 are distinct identifiers and must not substitute for the book"

record TraversalIdentifierBoundary : Set where
  constructor traversalIdentifierBoundary
  field
    cohnPublicationQidResolved : Bool
    harawayPublicationQidResolved : Bool
    blackwellPublicationQidResolved : Bool
    frickerPublicationQidResolved : Bool
    publicationQidEqualsAuthorQid : Bool
    conceptQidEqualsPublicationQid : Bool
    missingPublicationQidMeansPublicationAbsent : Bool

open TraversalIdentifierBoundary public

canonicalTraversalIdentifierBoundary : TraversalIdentifierBoundary
canonicalTraversalIdentifierBoundary = traversalIdentifierBoundary
  true true false false false false false

------------------------------------------------------------------------
-- Broad Dewey navigation parents.
-- These are subject-space coordinates, not verified publication-specific DDC
-- catalogue assignments.
------------------------------------------------------------------------

militaryScienceDewey : String
militaryScienceDewey = "355.000"

feminismGenderDewey : String
feminismGenderDewey = "305.420"

epistemologyDewey : String
epistemologyDewey = "121.000"

statisticsDewey : String
statisticsDewey = "519.500"

------------------------------------------------------------------------
-- Traversal coordinates.
------------------------------------------------------------------------

cohnTechnostrategicCoordinate : Ibrahim.DashiKnowledgeCoordinate
cohnTechnostrategicCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Culture/CohnTechnostrategicDiscourseExact.agda"
  "Cohn technostrategic discourse / abstraction fixture"
  militaryScienceDewey
  (Id.rawItemId cohnSexAndDeathPublicationQid)
  "doi:10.1086/494362"

situatedKnowledgeCoordinate : Ibrahim.DashiKnowledgeCoordinate
situatedKnowledgeCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "situated knowledge / partial perspective"
  feminismGenderDewey
  (Id.rawItemId harawaySituatedKnowledgesPublicationQid)
  "doi:10.2307/3178066"

epistemicInjusticeCoordinate : Ibrahim.DashiKnowledgeCoordinate
epistemicInjusticeCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "epistemic injustice / power and ethics of knowing"
  epistemologyDewey
  (Id.rawItemId epistemicInjusticeConceptQid)
  "doi:10.1093/acprof:oso/9780198237907.001.0001; QID is concept identity, not book identity"

blackwellComparisonCoordinate : Ibrahim.DashiKnowledgeCoordinate
blackwellComparisonCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "Blackwell comparison of experiments / decision-relative information"
  statisticsDewey
  "publication QID unresolved; author Q525037 retained separately"
  "doi:10.1214/aoms/1177729032"

leastCoordinateRepairCoordinate : Ibrahim.DashiKnowledgeCoordinate
leastCoordinateRepairCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Culture/CohnInstitutionalLeastCoordinateRepairExact.agda"
  "consumer-indexed least-coordinate repair and selective reopening"
  "repository Dewey parent should be taken from the generated repository projection; not guessed here"
  "no external QID asserted for the DASHI theorem"
  "DASHI.Culture.CohnInstitutionalLeastCoordinateRepairExact"

------------------------------------------------------------------------
-- Typed traversal edges.
-- These edges record the selected explanatory/search relation. They do not say
-- that the authors historically depended on one another or that one source
-- proves another source's claims.
------------------------------------------------------------------------

cohnToSituatedKnowledge : Ibrahim.DashiFirstLinkEdge
cohnToSituatedKnowledge = Ibrahim.dashi-first-link-edge
  cohnTechnostrategicCoordinate
  situatedKnowledgeCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Cohn's expert-discourse abstraction fixture and Haraway's situated-knowledge analysis meet at observer position / partial representation; this is a retrospective DASHI cross-pollination, not a claim of historical derivation or theoretical identity."
  true

situatedKnowledgeToEpistemicInjustice : Ibrahim.DashiFirstLinkEdge
situatedKnowledgeToEpistemicInjustice = Ibrahim.dashi-first-link-edge
  situatedKnowledgeCoordinate
  epistemicInjusticeCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Situated perspective and epistemic injustice supply adjacent questions about whose observations and interpretive resources remain legible. The edge is navigation/cross-pollination only and does not collapse the theories."
  true

blackwellToLeastCoordinateRepair : Ibrahim.DashiFirstLinkEdge
blackwellToLeastCoordinateRepair = Ibrahim.dashi-first-link-edge
  blackwellComparisonCoordinate
  leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Blackwell supplies primary decision-relative comparison-of-experiments precedent. DASHI independently constructs the finite missing-coordinate collision, candidate family, minimal eligible repair, Pareto proof and selective reopening relation."
  true

epistemicInjusticeToLeastCoordinateRepair : Ibrahim.DashiFirstLinkEdge
epistemicInjusticeToLeastCoordinateRepair = Ibrahim.dashi-first-link-edge
  epistemicInjusticeCoordinate
  leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Epistemic-injustice analysis motivates checking whether institutional observation surfaces exclude relevant testimony/concepts; it does not specify or prove DASHI's least-coordinate repair algorithm."
  true

------------------------------------------------------------------------
-- Highest-alpha traversal frontier.
------------------------------------------------------------------------

record InstitutionalTraversalFrontier : Set where
  constructor institutionalTraversalFrontier
  field
    proofFrontier : String
    sourceFrontier : String
    qidDebt : String
    deweyDebt : String
    paymentRule : String

open InstitutionalTraversalFrontier public

canonicalInstitutionalTraversalFrontier : InstitutionalTraversalFrontier
canonicalInstitutionalTraversalFrontier = institutionalTraversalFrontier
  "generic collision -> candidate coordinate debts -> minimal distinguishing coordinate set -> consumer-safe repair -> dependency-derived reopening"
  "continue Ibrahim/Dewey snowball only where a primary source can pay a newly identified conceptual/empirical premise or improve provenance/identity coverage"
  "Blackwell 1953 article publication QID and Fricker 2007 book publication QID remain unresolved in this traversal; author/concept QIDs are retained separately and cannot substitute"
  "publication-specific Dewey catalogue assignments remain unresolved; broad Dewey parents are navigation coordinates only, while the repository-generated Dewey projection remains authoritative for DASHI modules"
  "DOI/QID/Dewey/first-link navigation chooses where to inspect; only source-bounded propositions, typed dependencies, same-object receipts, and repository proofs pay conclusions"

------------------------------------------------------------------------
-- Direct reuse receipts / firewalls.
------------------------------------------------------------------------

coverageBoundary : Coverage.CoverageQualityBoundary
coverageBoundary = Coverage.canonicalCoverageQualityBoundary

traversalBoundary : Ibrahim.DashiKnowledgeTraversalBoundary
traversalBoundary = Ibrahim.canonicalDashiKnowledgeTraversalBoundary

leastRepairBoundary : Repair.LeastCoordinateRepairBoundary
leastRepairBoundary = Repair.canonicalLeastCoordinateRepairBoundary

record TraversalAttributionBoundary : Set where
  constructor traversalAttributionBoundary
  field
    deweyParentCreatesTheoremEdge : Bool
    qidCreatesProof : Bool
    doiCreatesDASHITheorem : Bool
    firstLinkCreatesHistoricalInfluenceClaim : Bool
    externalSourceOwnsLeastCoordinateRepair : Bool
    primarySourceCreatesLegalAuthority : Bool
    missingQidCreatesNegativeKnowledge : Bool
    traversalHighestAlphaFrontierIsTypedDependency : Bool

open TraversalAttributionBoundary public

canonicalTraversalAttributionBoundary : TraversalAttributionBoundary
canonicalTraversalAttributionBoundary = traversalAttributionBoundary
  false false false false false false false true

harawayCitationDoesNotImportProof :
  Source.citationImportsProof harawaySituatedKnowledges ≡ false
harawayCitationDoesNotImportProof = refl

blackwellCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority blackwellEquivalentComparisons ≡ false
blackwellCitationDoesNotCreateAuthority = refl

frickerCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority frickerEpistemicInjustice ≡ false
frickerCitationDoesNotCreateAuthority = refl

qidNamespaceBoundaryRetained : Id.IdentifierBoundary
qidNamespaceBoundaryRetained = Id.canonicalIdentifierBoundary
