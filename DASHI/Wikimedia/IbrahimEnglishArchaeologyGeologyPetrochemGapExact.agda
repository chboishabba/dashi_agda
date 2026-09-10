module DASHI.Wikimedia.IbrahimEnglishArchaeologyGeologyPetrochemGapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimEnglishAnthropologyHumanityBridgeExact as Anthropology

------------------------------------------------------------------------
-- IBRAHIM ENGLISH COVERAGE EXTENSION: ARCHAEOLOGY / GEOLOGY / PETROCHEMISTRY
--
-- Navigation prior:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI: 10.1016/j.jocs.2016.12.001
--
-- Ibrahim et al. showed that English-Wikipedia first-link flow tends from
-- specific topics toward general concepts, with high-flow funnels including
-- Community, State, Science and Philosophy, and topical accumulation around
-- Health Care and Fossil Fuel.  Their Fig. 1 example explicitly includes
-- Train -> Goods -> Economics -> Social Science -> ... -> Philosophy.
--
-- This owner uses that result as a coverage-search prior.  It distinguishes:
--   * genuinely missing discipline parent,
--   * direct parent/domain already present but narrow,
--   * substantial applied leaf content missing an explicit external bridge.
--
-- Current EN/Wikidata coordinates inspected 2026-09-10:
--   archaeology      Q23498
--   anthropology     Q23404
--   geology          Q1069
--   natural science  Q7991
--   petrochemistry   Q493630
--
-- Current EN Archaeology describes the discipline as study of human activity
-- through material culture and locates it among social science/humanities,
-- with common classification under anthropology, history or geography.
-- Current EN Geology explicitly calls geology a branch of natural science.
-- Wikidata Q493630 identifies petrochemistry as a branch of chemistry related
-- to petroleum.
------------------------------------------------------------------------

data CoverageShape : Set where
  canonicalParentPresent : CoverageShape
  narrowDomainPresent : CoverageShape
  appliedLeavesPresentMissingParentBridge : CoverageShape
  genuineDisciplineGap : CoverageShape

record ExternalDomainCoordinate : Set where
  constructor external-domain-coordinate
  field
    title : String
    qid : String
    externalParentTitle : String
    externalParentQid : String
    observationDate : String
    relationReading : String
open ExternalDomainCoordinate public

archaeologyCoordinate : ExternalDomainCoordinate
archaeologyCoordinate =
  external-domain-coordinate
    "Archaeology"
    "Q23498"
    "Anthropology / history / geography / social science"
    "Q23404; unresolved-history/geography/social-science-in-this-coordinate"
    "2026-09-10"
    "current EN classifies archaeology by material culture and human activity; anthropology is one major parent classification, not a universal identity"

geologyCoordinate : ExternalDomainCoordinate
geologyCoordinate =
  external-domain-coordinate
    "Geology"
    "Q1069"
    "natural science"
    "Q7991"
    "2026-09-10"
    "current EN and Wikidata place geology under natural science"

petrochemistryCoordinate : ExternalDomainCoordinate
petrochemistryCoordinate =
  external-domain-coordinate
    "petrochemistry"
    "Q493630"
    "chemistry"
    "qid-to-be-reused-from-canonical-Wikimedia-layer"
    "2026-09-10"
    "Wikidata identifies petrochemistry as a branch of chemistry related to petroleum"

------------------------------------------------------------------------
-- Repository-side introspection.
------------------------------------------------------------------------

record DomainCoverageAudit : Set where
  constructor domain-coverage-audit
  field
    coordinate : ExternalDomainCoordinate
    coverageShape : CoverageShape
    canonicalOwnerObserved : Bool
    reusableSubstrateObserved : Bool
    repositoryEvidence : String
    residual : String
open DomainCoverageAudit public

archaeologyAudit : DomainCoverageAudit
archaeologyAudit =
  domain-coverage-audit
    archaeologyCoordinate
    genuineDisciplineGap
    false
    true
    "focused repository search finds many uses of archaeology as proof/source-reconstruction terminology, but no canonical academic Archaeology owner; Anthropology audit already isolates archaeological/historical anthropology as unpaid"
    "add an archaeology discipline/source-method bridge over existing anthropology, history, geology/material, culture and provenance machinery; do not treat proof-search 'archaeology' strings as domain coverage"

geologyAudit : DomainCoverageAudit
geologyAudit =
  domain-coverage-audit
    geologyCoordinate
    narrowDomainPresent
    true
    true
    "DASHI/Geology/Everything.agda directly owns SaltGeochemistryExact, SaltConservationSpineExact and SaltBidiRegressionExact; geology also appears in environment and industrial-chemistry joins"
    "geology is not missing; expand beyond salt/geochemistry into stratigraphy, petrology, geophysics, geomorphology, tectonics and deep-time/source-backed parent bridges only where demanded"

petrochemistryAudit : DomainCoverageAudit
petrochemistryAudit =
  domain-coverage-audit
    petrochemistryCoordinate
    appliedLeavesPresentMissingParentBridge
    false
    true
    "DASHI/Chemistry/SaltPetroleumIndustrialChemistryNetworkExact.agda explicitly owns steam cracking, hydrocarbon feed, ethylene/propylene/aromatics and refinery/petrochemical transformation; IndustrialChemistryLogisticsEverything rolls the chain up"
    "petrochemical content is substantive; remaining debt is a canonical Petrochemistry/Chemistry parent coordinate and broader process/source coverage, not a new leaf domain from zero"

------------------------------------------------------------------------
-- Archaeology-specific bridge debt.
------------------------------------------------------------------------

data ArchaeologySurface : Set where
  materialCulture : ArchaeologySurface
  excavationSurvey : ArchaeologySurface
  chronologyDating : ArchaeologySurface
  humanPast : ArchaeologySurface
  heritageRepatriation : ArchaeologySurface
  geoarchaeology : ArchaeologySurface

record ArchaeologyResidual : Set where
  constructor archaeology-residual
  field
    surface : ArchaeologySurface
    reusableDashiNeighbour : String
    paid : Bool
    nextBridge : String
open ArchaeologyResidual public

materialCultureResidual : ArchaeologyResidual
materialCultureResidual =
  archaeology-residual materialCulture
    "culture/material/object/provenance carriers exist across DASHI"
    false
    "formalise archaeological object/context/provenance as a discipline-specific observation receipt"

excavationSurveyResidual : ArchaeologyResidual
excavationSurveyResidual =
  archaeology-residual excavationSurvey
    "general observer/acquisition machinery exists"
    false
    "add stratigraphic context, locus, sampling/excavation method and chain-of-custody coordinates; generic observation is insufficient"

chronologyDatingResidual : ArchaeologyResidual
chronologyDatingResidual =
  archaeology-residual chronologyDating
    "physics/chemistry/time and source-receipt machinery exist"
    false
    "route radiometric/relative/typological dating through method-specific uncertainty and calibration receipts"

humanPastResidual : ArchaeologyResidual
humanPastResidual =
  archaeology-residual humanPast
    "Anthropology/Humanity audit plus culture/history-adjacent content"
    false
    "weld archaeological inference to the existing humanity/culture lane without making anthropology and archaeology identical"

heritageRepatriationResidual : ArchaeologyResidual
heritageRepatriationResidual =
  archaeology-residual heritageRepatriation
    "Mabo, Indigenous-knowledge, law, authority and provenance surfaces"
    false
    "reuse rights/authority/provenance firewalls; source community and legal authority must remain explicit"

geoarchaeologyResidual : ArchaeologyResidual
geoarchaeologyResidual =
  archaeology-residual geoarchaeology
    "DASHI/Geology and Environment provide real physical substrate"
    false
    "bridge sediment/soil/landscape evidence into archaeological context rather than inventing a second geology"

------------------------------------------------------------------------
-- Funnel-level conclusion.
------------------------------------------------------------------------

record CrossDomainGapReading : Set where
  constructor cross-domain-gap-reading
  field
    archaeologyIsRealGap : Bool
    geologyIsRealGap : Bool
    petrochemistryIsRealGap : Bool
    geologyNeedsBreadthExpansion : Bool
    petrochemistryNeedsCanonicalParentBridge : Bool
    archaeologyCanReuseAnthropology : Bool
    archaeologyCanReuseGeology : Bool
    externalParentageCreatesProofDependency : Bool
open CrossDomainGapReading public

currentCrossDomainGapReading : CrossDomainGapReading
currentCrossDomainGapReading =
  cross-domain-gap-reading
    true false false true true true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RepositoryArchaeologyMeansAcademicArchaeology : Set where
data GeologySaltCoverageMeansCompleteGeology : Set where
data PetrochemicalProcessLeavesMeanCompletePetrochemistry : Set where
data AnthropologyParentMakesArchaeologyIdenticalToAnthropology : Set where

auditTerminologyDoesNotPayAcademicArchaeology :
  RepositoryArchaeologyMeansAcademicArchaeology → ⊥
auditTerminologyDoesNotPayAcademicArchaeology ()

saltGeologyDoesNotCompleteGeology :
  GeologySaltCoverageMeansCompleteGeology → ⊥
saltGeologyDoesNotCompleteGeology ()

processLeavesDoNotCompletePetrochemistry :
  PetrochemicalProcessLeavesMeanCompletePetrochemistry → ⊥
processLeavesDoNotCompletePetrochemistry ()

anthropologyParentDoesNotCollapseArchaeology :
  AnthropologyParentMakesArchaeologyIdenticalToAnthropology → ⊥
anthropologyParentDoesNotCollapseArchaeology ()

record ArchaeologyGeologyPetrochemBoundary : Set where
  constructor archaeology-geology-petrochem-boundary
  field
    ibrahimMethodIsNavigationPrior : Bool
    currentEnglishIsRevisionSensitive : Bool
    existingQidLayerReused : Bool
    archaeologyGapSeparatedFromRepoArchaeologyTerminology : Bool
    geologyExistingCoverageRetained : Bool
    petrochemistryExistingCoverageRetained : Bool
    wikipediaCreatesFormalAuthority : Bool
open ArchaeologyGeologyPetrochemBoundary public

canonicalArchaeologyGeologyPetrochemBoundary : ArchaeologyGeologyPetrochemBoundary
canonicalArchaeologyGeologyPetrochemBoundary =
  archaeology-geology-petrochem-boundary true true true true true true false
