module DASHI.Wikimedia.IbrahimEnglishParentCoverageGapAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.WikipediaFirstLinkNetworkExact as FLN
import DASHI.Wikimedia.ConceptEntityAlignmentExact as Alignment
import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Entity

------------------------------------------------------------------------
-- IBRAHIM ENGLISH-FIRST-LINK PARENT COVERAGE GAP ATLAS
--
-- Method source:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI: 10.1016/j.jocs.2016.12.001
--
-- Ibrahim et al. supply the navigation prior: first-link paths tend to move
-- from specific subjects toward increasingly general concepts, and traversal
-- funnels identify high-flow concepts.  This atlas uses that method to AUDIT
-- DASHI coverage, not to import Wikipedia's graph as theorem dependencies.
--
-- IMPORTANT SNAPSHOT BOUNDARY
-- The edges below are current English-Wikipedia observations inspected on
-- 2026-09-10.  They are NOT asserted to be the exact 2016/2017 Ibrahim dump
-- edges, because article revisions and parser/exclusion policy can change.
------------------------------------------------------------------------

data DashiParentCoverageStatus : Set where
  directParentOwner : DashiParentCoverageStatus
  strongLeafCoverageMissingParent : DashiParentCoverageStatus
  fragmentedIndirectCoverage : DashiParentCoverageStatus
  parentBridgeMissing : DashiParentCoverageStatus
  unresolvedAudit : DashiParentCoverageStatus

record EnglishParentProbe : Set where
  constructor english-parent-probe
  field
    childTitle : String
    childQid : String
    observedFirstParentTitle : String
    parentQid : String
    observationDate : String
    wikipediaPolicy : String
    dashiCoverageStatus : DashiParentCoverageStatus
    dashiEvidenceSurface : String
    gapReading : String
open EnglishParentProbe public

currentEnPolicy : String
currentEnPolicy =
  "current EN article body; first qualifying conceptual link after hatnote/disambiguation; audit seed only, not Ibrahim historical-edge identity"

psychologyToMind : EnglishParentProbe
psychologyToMind =
  english-parent-probe
    "Psychology"
    "Q9418"
    "mind"
    "Q450"
    "2026-09-10"
    currentEnPolicy
    strongLeafCoverageMissingParent
    "DASHI/Culture/LopezRiosMarxistPsychologySourceAtlasExact.agda; DASHI/Culture/LopezRiosExistingPsychologyCrossPollinationExact.agda; DASHI/Cognition/PNF/*"
    "psychology is already substantial; the gap is a canonical mind/psychology parent bridge into the existing cognition formulations"

sociologyToSociety : EnglishParentProbe
sociologyToSociety =
  english-parent-probe
    "Sociology"
    "Q21201"
    "society"
    "Q8425"
    "2026-09-10"
    currentEnPolicy
    fragmentedIndirectCoverage
    "DASHI/Cognition/PNF/CulturalMembershipBoundaryExact.agda; culture/governance/social-ecology source surfaces"
    "sociological sources and worked formulations exist, but no canonical Sociology/Society parent owner was found in the focused audit"

economicsToSocialScience : EnglishParentProbe
economicsToSocialScience =
  english-parent-probe
    "Economics"
    "Q8134"
    "social science"
    "Q34749"
    "2026-09-10"
    currentEnPolicy
    strongLeafCoverageMissingParent
    "DASHI/Economics/Everything.agda and DASHI/Economics/*"
    "economics has a direct formal domain; the missing seam is its explicit parent bridge into a shared social-science formulation"

anthropologyToHumanity : EnglishParentProbe
anthropologyToHumanity =
  english-parent-probe
    "Anthropology"
    "Q23404"
    "humanity"
    "Q1156970"
    "2026-09-10"
    currentEnPolicy
    parentBridgeMissing
    "focused search found anthropology language inside specialised Mabo/juridical material but no canonical Anthropology owner"
    "add an anthropology/humanity bridge only after reusing existing human, culture, biology, Mabo and social-ecology formulations"

politicalScienceToPolitics : EnglishParentProbe
politicalScienceToPolitics =
  english-parent-probe
    "Political science"
    "Q36442"
    "politics"
    "Q7163"
    "2026-09-10"
    currentEnPolicy
    parentBridgeMissing
    "law/governance/politics-adjacent formulations exist, but focused canonical PoliticalScience owner search returned no owner"
    "the gap is a typed political-science/politics parent bridge over existing Governance, SensibLaw, Mabo and political-economy material"

------------------------------------------------------------------------
-- Parent-of-parent probes expose the next bridge layer instead of stopping
-- after finding one Wikipedia parent.
------------------------------------------------------------------------

societyToIndividual : EnglishParentProbe
societyToIndividual =
  english-parent-probe
    "society"
    "Q8425"
    "individual"
    "unresolved-in-this-tranche"
    "2026-09-10"
    currentEnPolicy
    fragmentedIndirectCoverage
    "DASHI has individual/agent/observer carriers in cognition, provenance, law and core observer formulations"
    "current EN first qualifying concept is individual; resolve the exact external individual identity before choosing among person/agent/observer DASHI carriers"

socialScienceToScienceBranch : EnglishParentProbe
socialScienceToScienceBranch =
  english-parent-probe
    "social science"
    "Q34749"
    "branches of science"
    "unresolved-in-this-tranche"
    "2026-09-10"
    currentEnPolicy
    strongLeafCoverageMissingParent
    "science and natural-science formulations are spread across DASHI/Physics, Biology, Chemistry, Geology and methodology owners"
    "this is the highest-leverage common social funnel: a shared SocialScience owner can bind economics, sociology, anthropology, archaeology, political science, psychology, law, history and geography without pretending their methods are identical"

politicsToSociety : EnglishParentProbe
politicsToSociety =
  english-parent-probe
    "politics"
    "Q7163"
    "society"
    "Q8425"
    "2026-09-10"
    currentEnPolicy
    fragmentedIndirectCoverage
    "DASHI/Governance/*; SensibLaw; Mabo/native-title; political-economy and capital formulations"
    "Political science now has a current EN path politics -> society -> individual; the missing work is canonical bridge ownership, not new political leaf facts"

------------------------------------------------------------------------
-- Natural-science probes.  These distinguish true absence from broad domain
-- ownership whose only debt is an explicit parent bridge.
------------------------------------------------------------------------

archaeologyToHumanActivity : EnglishParentProbe
archaeologyToHumanActivity =
  english-parent-probe
    "Archaeology"
    "Q23498"
    "human activity"
    "Q24902509"
    "2026-09-10"
    currentEnPolicy
    parentBridgeMissing
    "focused Archaeology search returned proof/repository-archaeology usages but no archaeological domain owner; anthropology/history/culture/geology/material-analysis substrates already exist"
    "genuine parent-owner gap: bridge archaeology across human activity, material culture, anthropology, history/geography and geoscience rather than creating an isolated archaeology silo"

geologyToNaturalScience : EnglishParentProbe
geologyToNaturalScience =
  english-parent-probe
    "Geology"
    "Q1069"
    "natural science"
    "Q7991"
    "2026-09-10"
    currentEnPolicy
    directParentOwner
    "DASHI/Geology/Everything.agda; SaltGeochemistryExact; SaltConservationSpineExact; environmental geology/geomorphology cross-pollinations"
    "geology is already a direct formal domain; retain only the explicit Geology -> NaturalScience bridge debt"

chemistryToMatter : EnglishParentProbe
chemistryToMatter =
  english-parent-probe
    "Chemistry"
    "Q2329"
    "matter"
    "Q35758"
    "2026-09-10"
    currentEnPolicy
    directParentOwner
    "DASHI/Chemistry/Everything.agda; TransitionKernel; industrial chemistry, chlor-alkali, assay and molecular-mechanism surfaces"
    "chemistry is not a coverage gap; the Ibrahim path identifies matter as its external parent coordinate and exposes only a parent-weld audit"

naturalScienceToScience : EnglishParentProbe
naturalScienceToScience =
  english-parent-probe
    "Natural science"
    "Q7991"
    "science"
    "Q336"
    "2026-09-10"
    currentEnPolicy
    fragmentedIndirectCoverage
    "Physics, Biology, Chemistry, Geology, Environment and scientific-method/source-diligence surfaces"
    "the shared natural-science funnel is broad but fragmented; select a canonical Science/NaturalScience bridge instead of adding another scientific leaf hierarchy"

------------------------------------------------------------------------
-- Petrochemistry is intentionally NOT encoded as an English first-link edge.
-- Wikidata Q493630 identifies petrochemistry as a branch of chemistry, while
-- the audited item has no EN Wikipedia sitelink.  DASHI already has explicit
-- petroleum/refinery/petrochemical chemistry content, so absence from the EN
-- seed graph must not be mistaken for a DASHI subject gap.
------------------------------------------------------------------------

record NonEnSeedDisposition : Set where
  constructor non-en-seed-disposition
  field
    conceptTitle : String
    conceptQid : String
    externalParentTitle : String
    externalParentQid : String
    englishFirstLinkAvailable : Bool
    dashiDomainPresent : Bool
    dashiEvidence : String
    disposition : String
open NonEnSeedDisposition public

petrochemistryDisposition : NonEnSeedDisposition
petrochemistryDisposition =
  non-en-seed-disposition
    "petrochemistry"
    "Q493630"
    "chemistry"
    "Q2329"
    false
    true
    "DASHI/Chemistry/SaltPetroleumIndustrialChemistryNetworkExact.agda; DASHI/IndustrialChemistryLogisticsEverything.agda"
    "retain Wikidata parent identity and DASHI coverage; do not manufacture an Ibrahim EN first-link observation"

------------------------------------------------------------------------
-- Existing QID atlas reuse receipts.  The strings carried by EnglishParentProbe
-- are observation payloads; canonical external identities live in the shared
-- ScientificReferenceEntityAtlasExact owner.
------------------------------------------------------------------------

record ParentEntityReuseReceipt : Set where
  constructor parent-entity-reuse-receipt
  field
    auditRole : String
    entity : Entity.ScientificReferenceEntity
open ParentEntityReuseReceipt public

socialScienceEntityReuse societyEntityReuse politicsEntityReuse : ParentEntityReuseReceipt
archaeologyEntityReuse humanActivityEntityReuse : ParentEntityReuseReceipt
geologyEntityReuse chemistryEntityReuse petrochemistryEntityReuse : ParentEntityReuseReceipt
matterEntityReuse naturalScienceEntityReuse scienceEntityReuse : ParentEntityReuseReceipt
socialScienceEntityReuse = parent-entity-reuse-receipt "shared social-science funnel" Entity.socialScience
societyEntityReuse = parent-entity-reuse-receipt "sociology/politics convergence parent" Entity.society
politicsEntityReuse = parent-entity-reuse-receipt "political-science parent" Entity.politics
archaeologyEntityReuse = parent-entity-reuse-receipt "archaeology gap seed" Entity.archaeology
humanActivityEntityReuse = parent-entity-reuse-receipt "archaeology first parent" Entity.humanActivity
geologyEntityReuse = parent-entity-reuse-receipt "geology domain seed" Entity.geology
chemistryEntityReuse = parent-entity-reuse-receipt "chemistry domain seed" Entity.chemistry
petrochemistryEntityReuse = parent-entity-reuse-receipt "petrochemistry non-EN seed" Entity.petrochemistry
matterEntityReuse = parent-entity-reuse-receipt "chemistry first parent" Entity.matter
naturalScienceEntityReuse = parent-entity-reuse-receipt "geology/science funnel" Entity.naturalScience
scienceEntityReuse = parent-entity-reuse-receipt "natural-science parent" Entity.science

------------------------------------------------------------------------
-- Gap-priority semantics.
------------------------------------------------------------------------

record EnglishCoverageGapPriority : Set where
  constructor english-coverage-gap-priority
  field
    psychologyNeedsNewLeafTheory : Bool
    psychologyNeedsParentBridge : Bool
    sociologyNeedsCanonicalParent : Bool
    economicsNeedsNewLeafDomain : Bool
    economicsNeedsSocialScienceBridge : Bool
    anthropologyNeedsCanonicalParent : Bool
    politicalScienceNeedsCanonicalParent : Bool
    archaeologyNeedsCanonicalParent : Bool
    geologyNeedsNewLeafDomain : Bool
    chemistryNeedsNewLeafDomain : Bool
    petrochemistryNeedsNewLeafDomain : Bool
    socialScienceCommonFunnelIsPriority : Bool
    naturalScienceCommonFunnelNeedsBridgeAudit : Bool
open EnglishCoverageGapPriority public

firstCoveragePriority : EnglishCoverageGapPriority
firstCoveragePriority =
  english-coverage-gap-priority
    false true true false true true true true false false false true true

------------------------------------------------------------------------
-- Firewalls: navigation evidence discovers coverage debt; it never promotes
-- Wikipedia adjacency into semantic identity, proof dependency or historical
-- Ibrahim-edge identity.
------------------------------------------------------------------------

data CurrentEnglishEdgeIsIbrahimHistoricalEdge : Set where
data WikipediaParentCreatesDashiProofDependency : Set where
data MissingCanonicalParentMeansNoDomainKnowledge : Set where
data QidCreatesDashiDefinition : Set where
data MissingEnglishSitelinkMeansMissingDashiDomain : Set where

currentEdgeDoesNotBecomeHistoricalIbrahimEdge :
  CurrentEnglishEdgeIsIbrahimHistoricalEdge → ⊥
currentEdgeDoesNotBecomeHistoricalIbrahimEdge ()

wikipediaParentDoesNotCreateProofDependency :
  WikipediaParentCreatesDashiProofDependency → ⊥
wikipediaParentDoesNotCreateProofDependency ()

missingParentDoesNotEraseLeafKnowledge :
  MissingCanonicalParentMeansNoDomainKnowledge → ⊥
missingParentDoesNotEraseLeafKnowledge ()

qidDoesNotCreateDashiDefinition : QidCreatesDashiDefinition → ⊥
qidDoesNotCreateDashiDefinition ()

missingEnglishSitelinkDoesNotEraseDashiDomain :
  MissingEnglishSitelinkMeansMissingDashiDomain → ⊥
missingEnglishSitelinkDoesNotEraseDashiDomain ()

record IbrahimEnglishCoverageAuditBoundary : Set where
  constructor ibrahim-english-coverage-audit-boundary
  field
    ibrahimMethodAttributed : Bool
    currentEnglishEdgesRevisionSensitive : Bool
    existingQidLayerReused : Bool
    leafCoverageSeparatedFromParentCoverage : Bool
    missingEnSeedSeparatedFromMissingDomain : Bool
    wikipediaEdgesCreateProofDependencies : Bool
    missingParentErasesExistingKnowledge : Bool

canonicalIbrahimEnglishCoverageAuditBoundary : IbrahimEnglishCoverageAuditBoundary
canonicalIbrahimEnglishCoverageAuditBoundary =
  ibrahim-english-coverage-audit-boundary true true true true true false false
