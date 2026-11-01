module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionTwoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalExact as Traversal
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionExact as Prior
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim

------------------------------------------------------------------------
-- SECOND IBRAHIM / DEWEY ACQUISITION EXTENSION
--
-- Append-only acquisition of three additional primary conceptual leaves:
--
--   Tuana    : ignorance may be constructed, maintained and disseminated;
--   Pohlhaus : situated/interdependent knowers may refuse marginal epistemic tools;
--   Anderson : feminist epistemology as social/naturalized internal critique
--              of knowledge-production norms and interests.
--
-- These sources supply bounded candidate coordinate families only. They do
-- not prove a particular institutional collision, bad faith, legal outcome,
-- least-coordinate repair, Pareto selection or reopening theorem.
------------------------------------------------------------------------

tuanaComingToUnderstand : Source.AttributedSource
tuanaComingToUnderstand = Source.mkDOISource
  "Nancy Tuana"
  "Coming to Understand: Orgasm and the Epistemology of Ignorance"
  "Hypatia 19(1), 194-232"
  "2004"
  "10.1111/j.1527-2001.2004.tb01275.x"
  "https://doi.org/10.1111/j.1527-2001.2004.tb01275.x"
  Source.academicArticleSource
  "Primary conceptual source for epistemologies of ignorance: ignorance may be constructed, maintained and disseminated and can interact with cognitive authority, doubt, trust, silencing and uncertainty. It motivates an ignorance-production coordinate family; it does not establish any specific institutional ignorance mechanism or DASHI repair theorem."
  Source.publicAttribution

pohlhausWillfulHermeneuticalIgnorance : Source.AttributedSource
pohlhausWillfulHermeneuticalIgnorance = Source.mkDOISource
  "Gaile Pohlhaus Jr."
  "Relational Knowing and Epistemic Injustice: Toward a Theory of Willful Hermeneutical Ignorance"
  "Hypatia 27(4), 715-735"
  "2012"
  "10.1111/j.1527-2001.2011.01222.x"
  "https://doi.org/10.1111/j.1527-2001.2011.01222.x"
  Source.academicArticleSource
  "Primary conceptual source for willful hermeneutical ignorance arising when dominantly situated knowers refuse epistemic tools developed from marginalized experience. It motivates a hermeneutical-refusal coordinate family; it does not prove bad faith or a specific institutional refusal in any DASHI application."
  Source.publicAttribution

andersonFeministEpistemology : Source.AttributedSource
andersonFeministEpistemology = Source.mkDOISource
  "Elizabeth Anderson"
  "Feminist Epistemology: An Interpretation and a Defense"
  "Hypatia 10(3), 50-84"
  "1995"
  "10.1111/j.1527-2001.1995.tb00737.x"
  "https://doi.org/10.1111/j.1527-2001.1995.tb00737.x"
  Source.academicArticleSource
  "Primary conceptual source framing feminist epistemology as naturalized social epistemology concerned with how gendered norms, interests and experience shape knowledge production and enable internal critique. It motivates a critical-uptake / production-context coordinate family; it creates neither institutional authority nor a DASHI adequacy theorem."
  Source.publicAttribution

acquisitionExtensionTwoAtlas : Source.AttributedSourceAtlas
acquisitionExtensionTwoAtlas = Source.mkSourceAtlas
  "Cohn institutional Ibrahim/Dewey acquisition extension two"
  "DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionTwoExact"
  (tuanaComingToUnderstand ∷
   pohlhausWillfulHermeneuticalIgnorance ∷
   andersonFeministEpistemology ∷ [])
  "Append-only primary-source extension for constructed ignorance, willful hermeneutical refusal and social/internal critique of knowledge production. Source identity and conceptual relevance remain distinct from theorem ownership, case-specific facts, legal authority, motive and causal inference."

------------------------------------------------------------------------
-- Identifier state.
------------------------------------------------------------------------

nancyTuanaAuthorQid : Id.ItemId
nancyTuanaAuthorQid = Id.itemId "Q27451854"

elizabethAndersonAuthorQid : Id.ItemId
elizabethAndersonAuthorQid = Id.itemId "Q1331312"

tuanaPublicationIdentity : Traversal.ItemResolution
tuanaPublicationIdentity = Traversal.unresolvedItem
  "publication-item QID for Coming to Understand not verified in this pass; Nancy Tuana author Q27451854 is retained separately"

pohlhausPublicationIdentity : Traversal.ItemResolution
pohlhausPublicationIdentity = Traversal.unresolvedItem
  "publication-item QID for Relational Knowing and Epistemic Injustice not verified in this pass"

pohlhausPersonIdentity : Traversal.ItemResolution
pohlhausPersonIdentity = Traversal.unresolvedItem
  "person QID for philosopher Gaile Pohlhaus Jr. not verified in this pass; no same-name QID is promoted by string match"

andersonPublicationIdentity : Traversal.ItemResolution
andersonPublicationIdentity = Traversal.unresolvedItem
  "publication-item QID for Feminist Epistemology: An Interpretation and a Defense not verified in this pass; Elizabeth Anderson author Q1331312 is retained separately"

record AcquisitionTwoIdentifierBoundary : Set where
  constructor acquisitionTwoIdentifierBoundary
  field
    tuanaAuthorQidResolved : Bool
    tuanaPublicationQidResolved : Bool
    pohlhausPersonQidResolved : Bool
    pohlhausPublicationQidResolved : Bool
    andersonAuthorQidResolved : Bool
    andersonPublicationQidResolved : Bool
    sameNameMayPromotePersonQid : Bool
    authorQidMaySubstitutePublicationQid : Bool

open AcquisitionTwoIdentifierBoundary public

canonicalAcquisitionTwoIdentifierBoundary : AcquisitionTwoIdentifierBoundary
canonicalAcquisitionTwoIdentifierBoundary =
  acquisitionTwoIdentifierBoundary true false false false true false false false

------------------------------------------------------------------------
-- Broad subject-space navigation only.
------------------------------------------------------------------------

socialEpistemologyDewey : String
socialEpistemologyDewey = "121.000"

feministTheoryDewey : String
feministTheoryDewey = "305.420"

------------------------------------------------------------------------
-- Candidate coordinate families.
------------------------------------------------------------------------

tuanaIgnoranceProductionCoordinate : Ibrahim.DashiKnowledgeCoordinate
tuanaIgnoranceProductionCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "constructed / maintained / disseminated ignorance"
  socialEpistemologyDewey
  "publication QID unresolved; Nancy Tuana author Q27451854 retained separately"
  "doi:10.1111/j.1527-2001.2004.tb01275.x"

pohlhausHermeneuticalRefusalCoordinate : Ibrahim.DashiKnowledgeCoordinate
pohlhausHermeneuticalRefusalCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "willful hermeneutical ignorance / refusal of marginal epistemic tools"
  socialEpistemologyDewey
  "publication and person QIDs unresolved"
  "doi:10.1111/j.1527-2001.2011.01222.x"

andersonCriticalUptakeCoordinate : Ibrahim.DashiKnowledgeCoordinate
andersonCriticalUptakeCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "social epistemology / internal critique of knowledge-production norms and interests"
  feministTheoryDewey
  "publication QID unresolved; Elizabeth Anderson author Q1331312 retained separately"
  "doi:10.1111/j.1527-2001.1995.tb00737.x"

------------------------------------------------------------------------
-- Typed traversal into the existing least-coordinate diagnosis frontier.
------------------------------------------------------------------------

tuanaToIgnoranceProduction : Ibrahim.DashiFirstLinkEdge
tuanaToIgnoranceProduction = Ibrahim.dashi-first-link-edge
  tuanaIgnoranceProductionCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Tuana makes ignorance-production mechanisms a candidate coordinate family when a collision cannot be explained by mere absence of data. DASHI must still prove which mechanism, if any, distinguishes the consumer fibre."
  true

pohlhausToHermeneuticalRefusal : Ibrahim.DashiFirstLinkEdge
pohlhausToHermeneuticalRefusal = Ibrahim.dashi-first-link-edge
  pohlhausHermeneuticalRefusalCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Pohlhaus makes refusal or non-acknowledgement of marginal epistemic tools a candidate coordinate family distinct from simple testimony non-uptake. No individual or institution is assigned motive or bad faith by this edge."
  true

andersonToCriticalUptake : Ibrahim.DashiFirstLinkEdge
andersonToCriticalUptake = Ibrahim.dashi-first-link-edge
  andersonCriticalUptakeCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Anderson makes norms, interests and internal critical uptake in knowledge production candidate coordinates when institutional evidence surfaces appear locally adequate but downstream critique differs. The source does not supply the DASHI collision or authority."
  true

------------------------------------------------------------------------
-- Attribution / inference firewall.
------------------------------------------------------------------------

record AcquisitionTwoAttributionBoundary : Set where
  constructor acquisitionTwoAttributionBoundary
  field
    constructedIgnoranceEqualsSimpleMissingData : Bool
    willfulIgnoranceSourceProvesSpecificBadFaith : Bool
    feministEpistemologyCreatesInstitutionalAuthority : Bool
    sourceAdjacencyCreatesHistoricalInfluence : Bool
    acquiredSourcesOwnDashiRepairTheorem : Bool
    unresolvedQidCreatesNegativeKnowledge : Bool
    acquisitionAddsDistinctCandidateCoordinateFamilies : Bool

open AcquisitionTwoAttributionBoundary public

canonicalAcquisitionTwoAttributionBoundary : AcquisitionTwoAttributionBoundary
canonicalAcquisitionTwoAttributionBoundary =
  acquisitionTwoAttributionBoundary false false false false false false true

tuanaCitationDoesNotImportProof :
  Source.citationImportsProof tuanaComingToUnderstand ≡ false
tuanaCitationDoesNotImportProof = refl

pohlhausCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority pohlhausWillfulHermeneuticalIgnorance ≡ false
pohlhausCitationDoesNotCreateAuthority = refl

andersonCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority andersonFeministEpistemology ≡ false
andersonCitationDoesNotCreateAuthority = refl

------------------------------------------------------------------------
-- Updated acquisition frontier.
------------------------------------------------------------------------

record AcquisitionTwoFrontier : Set where
  constructor acquisitionTwoFrontier
  field
    priorFamilies : String
    addedFamilies : String
    nextProofUse : String
    identifierDebt : String
    stopRule : String

open AcquisitionTwoFrontier public

canonicalAcquisitionTwoFrontier : AcquisitionTwoFrontier
canonicalAcquisitionTwoFrontier = acquisitionTwoFrontier
  "evidential context/criticism; testimony uptake/silencing; plural interpretive resources"
  "constructed ignorance; willful hermeneutical refusal; social/internal critical uptake in knowledge production"
  "for a concrete institutional collision, test these candidate families together with the prior acquisition families; only coordinates that actually separate the unpaid fibre may enter the minimal repair search"
  "publication QIDs for Tuana 2004, Pohlhaus 2012 and Anderson 1995 remain unresolved; Pohlhaus person QID remains unresolved; verified author QIDs cannot substitute for publication identities"
  "continue acquisition only for a distinct failure mode, source/provenance identity payment, or empirically required premise; stop when new papers merely rename an already represented coordinate family"

-- Thin import witness: the previous acquisition snapshot remains an independent
-- parent rather than being rewritten by this extension.
priorAcquisitionBoundary : Prior.AcquisitionAttributionBoundary
priorAcquisitionBoundary = Prior.canonicalAcquisitionAttributionBoundary
