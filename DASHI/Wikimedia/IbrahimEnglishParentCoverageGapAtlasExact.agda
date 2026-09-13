module DASHI.Wikimedia.IbrahimEnglishParentCoverageGapAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.WikipediaFirstLinkNetworkExact as FLN
import DASHI.Wikimedia.ConceptEntityAlignmentExact as Alignment

------------------------------------------------------------------------
-- IBRAHIM ENGLISH-FIRST-LINK PARENT COVERAGE GAP ATLAS
--
-- Method source:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI: 10.1016/j.jocs.2016.12.001
-- arXiv:1605.00309
--
-- Ibrahim et al. supply the navigation prior: first-link paths tend to move
-- from specific subjects toward increasingly general concepts, and traversal
-- funnels identify high-flow concepts.  This atlas uses that method to AUDIT
-- DASHI coverage, not to import Wikipedia's graph as theorem dependencies.
--
-- IMPORTANT SNAPSHOT BOUNDARY
-- The edges below are current English-Wikipedia observations inspected on
-- 2026-09-10/11.  They are NOT asserted to be the exact 2016/2017 Ibrahim dump
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
    "Q795052"
    "2026-09-11"
    currentEnPolicy
    fragmentedIndirectCoverage
    "DASHI has individual/agent/observer carriers in multiple domains"
    "Wikidata Q795052 resolves the semantic coordinate for individual. The remaining debt is quotienting that coordinate against existing agent/person/observer formulations; QID identity does not choose the DASHI owner."

socialScienceToScienceBranch : EnglishParentProbe
socialScienceToScienceBranch =
  english-parent-probe
    "social science"
    "Q34749"
    "branch of science"
    "Q2465832"
    "2026-09-11"
    currentEnPolicy
    fragmentedIndirectCoverage
    "science and natural-science formulations are spread across DASHI/Physics, Biology, Chemistry and methodology owners"
    "Wikidata Q2465832 resolves the branch-of-science semantic coordinate. The high-value gap remains selecting/reusing a repo-wide science formulation owner rather than creating a directory-label ontology."

------------------------------------------------------------------------
-- Gap-priority semantics.
------------------------------------------------------------------------

record EnglishSocialScienceGapPriority : Set where
  constructor english-social-science-gap-priority
  field
    psychologyNeedsNewLeafTheory : Bool
    psychologyNeedsParentBridge : Bool
    sociologyNeedsCanonicalParent : Bool
    economicsNeedsNewLeafDomain : Bool
    economicsNeedsSocialScienceBridge : Bool
    anthropologyNeedsCanonicalParent : Bool
    politicalScienceNeedsCanonicalParent : Bool
    socialScienceCommonFunnelIsPriority : Bool
open EnglishSocialScienceGapPriority public

firstSocialSciencePriority : EnglishSocialScienceGapPriority
firstSocialSciencePriority =
  english-social-science-gap-priority
    false true true false true true true true

------------------------------------------------------------------------
-- Firewalls: navigation evidence discovers coverage debt; it never promotes
-- Wikipedia adjacency into semantic identity, proof dependency or historical
-- Ibrahim-edge identity.
------------------------------------------------------------------------

data CurrentEnglishEdgeIsIbrahimHistoricalEdge : Set where
data WikipediaParentCreatesDashiProofDependency : Set where
data MissingCanonicalParentMeansNoDomainKnowledge : Set where
data QidCreatesDashiDefinition : Set where

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

record IbrahimEnglishCoverageAuditBoundary : Set where
  constructor ibrahim-english-coverage-audit-boundary
  field
    ibrahimMethodAttributed : Bool
    currentEnglishEdgesRevisionSensitive : Bool
    existingQidLayerReused : Bool
    leafCoverageSeparatedFromParentCoverage : Bool
    parentSemanticQidsResolvedForCurrentSecondLayer : Bool
    wikipediaEdgesCreateProofDependencies : Bool
    missingParentErasesExistingKnowledge : Bool

canonicalIbrahimEnglishCoverageAuditBoundary : IbrahimEnglishCoverageAuditBoundary
canonicalIbrahimEnglishCoverageAuditBoundary =
  ibrahim-english-coverage-audit-boundary true true true true true false false
