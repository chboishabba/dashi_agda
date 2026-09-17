module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFiveExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalExact as Traversal
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFourExact as Prior
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionThreeExact as Three
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim

------------------------------------------------------------------------
-- FIFTH IBRAHIM / QID / DEWEY ACQUISITION EXTENSION
--
-- Pareto follow from the Two-Eyed / epistemic-labour branches.
--
-- Reid et al. 2024 is admitted because it adds a distinct institutional
-- research-relationship coordinate: including Indigenous knowledge or inviting
-- Indigenous partners does not by itself establish an ethical/equitable
-- relation, discharge relational labour, respect rights/permission, or supply
-- the systemic resources needed for that relation.
--
-- This source is not collapsed into Berenstain's epistemic-exploitation
-- concept, nor into the 2021 Two-Eyed Seeing coexistence source. It provides a
-- source-bounded related manifestation with its own research/rights context.
------------------------------------------------------------------------

reidResearchInAGoodWay : Source.AttributedSource
reidResearchInAGoodWay = Source.mkDOISource
  "Andrea J. Reid; Deborah A. McGregor; Allyson K. Menzies; Lauren E. Eckert; Catherine M. Febria; Jesse N. Popp"
  "Ecological research 'in a good way' means ethical and equitable relationships with Indigenous Peoples and Lands"
  "Nature Ecology & Evolution 8, 595-598"
  "2024"
  "10.1038/s41559-023-02309-0"
  "https://doi.org/10.1038/s41559-023-02309-0"
  Source.academicArticleSource
  "Primary research-ethics commentary arguing that growing engagement with Indigenous Peoples and knowledge systems carries risk, burden and peril and requires ethical/equitable relationships, systemic support and attention to relational labour. It motivates a rights-holder/relationship/burden coordinate distinct from merely including an Indigenous knowledge surface. It does not adjudicate any specific institution, transfer community authority, or prove a DASHI repair theorem."
  Source.publicAttribution

acquisitionExtensionFiveAtlas : Source.AttributedSourceAtlas
acquisitionExtensionFiveAtlas = Source.mkSourceAtlas
  "Cohn institutional Ibrahim/QID/Dewey acquisition extension five"
  "DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFiveExact"
  (reidResearchInAGoodWay ∷ [])
  "Single Pareto leaf for ethical/equitable Indigenous research relationship, rights/burden and relational labour. The source is kept distinct from generic epistemic labour, Two-Eyed coexistence, consent, permission, benefit sharing, institutional fact and theorem authority."

------------------------------------------------------------------------
-- QID / Dewey identity state.
------------------------------------------------------------------------

reid2024IdentifierState : String
reid2024IdentifierState =
  "publication-item QID and author QIDs unresolved in this pass; DOI 10.1038/s41559-023-02309-0 is retained as bibliographic identity; ORCID or other author identifiers are not substituted for Wikidata QIDs"

reid2024DeweyState : String
reid2024DeweyState =
  "publication-specific Dewey assignment unresolved; no neighbouring Indigenous-knowledge or ecology class is promoted as if inspected on the publication record"

------------------------------------------------------------------------
-- Candidate coordinate family.
------------------------------------------------------------------------

reidRelationalResearchBurdenCoordinate : Ibrahim.DashiKnowledgeCoordinate
reidRelationalResearchBurdenCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary research-ethics source coordinate"
  "Indigenous rights-holder relation / ethical-equitable research relation / relational labour and burden"
  "Dewey unresolved for publication-specific classification"
  "publication and author QIDs unresolved"
  "doi:10.1038/s41559-023-02309-0"

reidToRelationalResearchBurden : Ibrahim.DashiFirstLinkEdge
reidToRelationalResearchBurden = Ibrahim.dashi-first-link-edge
  reidRelationalResearchBurdenCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "A consumer can observe Indigenous knowledge inclusion or partnership while the underlying relationship still differs in rights, burden, permission, relational labour or systemic support. This coordinate is admitted only after an actual fibre demonstrates that difference."
  true

------------------------------------------------------------------------
-- Cross-pollination without identity collapse.
------------------------------------------------------------------------

priorTwoEyedBoundary : Prior.AcquisitionFourBoundary
priorTwoEyedBoundary = Prior.canonicalAcquisitionFourBoundary

priorEpistemicLabourBoundary : Three.AcquisitionThreeBoundary
priorEpistemicLabourBoundary = Three.canonicalAcquisitionThreeBoundary

record AcquisitionFiveBoundary : Set where
  constructor acquisition-five-boundary
  field
    indigenousRelationalResearchBurdenAdded : Bool
    knowledgeIncludedImpliesEthicalEquitableRelation : Bool
    engagementImpliesConsentOrPermission : Bool
    indigenousRightsHolderMayBeFlattenedToGenericStakeholder : Bool
    reidRelationalLabourDefinitionallyEqualsBerenstainEpistemicLabour : Bool
    twoEyedCoexistenceDefinitionallyEqualsResearchEthics : Bool
    sourceAdjacencyAutomaticallySelectsResidual : Bool
    sourceCreatesInstitutionalFact : Bool
    unverifiedPublicationQidMayBeInvented : Bool
    deweyNeighbourMaySubstituteVerifiedPublicationClass : Bool

open AcquisitionFiveBoundary public

canonicalAcquisitionFiveBoundary : AcquisitionFiveBoundary
canonicalAcquisitionFiveBoundary = acquisition-five-boundary
  true
  false false false false false false false false false

reidCitationDoesNotImportProof :
  Source.citationImportsProof reidResearchInAGoodWay ≡ false
reidCitationDoesNotImportProof = refl

reidCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority reidResearchInAGoodWay ≡ false
reidCitationDoesNotCreateAuthority = refl

------------------------------------------------------------------------
-- Pareto frontier after the fifth follow.
------------------------------------------------------------------------

record AcquisitionFiveFrontier : Set where
  constructor acquisition-five-frontier
  field
    addedFamily : String
    relatedButNonidenticalFamilies : String
    deferredSources : String
    qidDeweyDebt : String
    nextProofUse : String
    stopRule : String

open AcquisitionFiveFrontier public

canonicalAcquisitionFiveFrontier : AcquisitionFiveFrontier
canonicalAcquisitionFiveFrontier = acquisition-five-frontier
  "ethical/equitable Indigenous research relation with rights-holder, relational-labour, burden and systemic-support coordinates"
  "Berenstain epistemic labour burden; Reid et al. 2021 Two-Eyed coexistence/co-production; permission/obligation/benefit-sharing owners remain related but definitionally separate"
  "Anderson 2012 system-level epistemic justice, Fraser 1990 counterpublics and Ermine 2007 ethical space are retained as useful follow candidates but not admitted here because they presently overlap more strongly with existing structural-exclusion, activism/internal-exclusion and Two-Eyed interface families"
  "Reid 2024 publication and author QIDs unresolved; publication-specific Dewey unresolved; no identifier or neighbouring class is invented"
  "test whether a real institutional fibre can hold knowledge inclusion/presence fixed while differing in rights-holder relation, relational burden or systemic support; only a separating coordinate may enter repair or next-probe scheduling"
  "stop this branch unless a new source adds a consumer-relevant failure mode beyond coexistence, permission, obligation, participation power, epistemic labour and relational research burden"
