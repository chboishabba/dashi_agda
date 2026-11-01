module DASHI.Governance.EvidenceGradedGenealogyCasesExact where

------------------------------------------------------------------------
-- BOUNDED CASE INSTANTIATIONS
--
-- This module deliberately demonstrates different evidence grades rather than
-- forcing heterogeneous political/cultural cases into one pipeline.
--
-- Primary/bounded sources used:
--   Laura A. Schmidt,
--   "Tobacco Industry Contributions to the Development of Ultraprocessed Food
--   in the United States, 1985-2007: A Case Study of Lunchables",
--   American Journal of Public Health 116(7):940-949 (2026),
--   DOI 10.2105/AJPH.2026.308491.
--
--   Naomi Oreskes; Erik M. Conway,
--   "Merchants of Doubt: How a Handful of Scientists Obscured the Truth on
--   Issues from Tobacco Smoke to Global Warming", Bloomsbury Press (2010),
--   ISBN 978-1-59691-610-4; no DOI asserted for the book.
--
--   Giovanna Parmigiani,
--   "Magic and Politics: Conspirituality and COVID-19",
--   Journal of the American Academy of Religion 89(2):506-529 (2021),
--   DOI 10.1093/jaarel/lfab053.
--
--   Michael Givel,
--   "Consent and counter-mobilization: the case of the national smokers
--   alliance", Journal of Health Communication 12(4):339-357 (2007),
--   DOI 10.1080/10810730701326002.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources
import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy

------------------------------------------------------------------------
-- Nodes.
------------------------------------------------------------------------

tobaccoIndustry : Genealogy.GenealogyNode
tobaccoIndustry = Genealogy.genealogyNode "tobacco industry R&D / influence infrastructure" Genealogy.institution

ultraprocessedFoodRAndD : Genealogy.GenealogyNode
ultraprocessedFoodRAndD = Genealogy.genealogyNode "ultraprocessed-food product-development infrastructure" Genealogy.institution

climateDenialCampaigns : Genealogy.GenealogyNode
climateDenialCampaigns = Genealogy.genealogyNode "climate-change doubt / denial campaigns" Genealogy.narrative

nationalSmokersAlliance : Genealogy.GenealogyNode
nationalSmokersAlliance = Genealogy.genealogyNode "National Smokers Alliance counter-mobilization" Genealogy.organisation

consentEngineeringTechnique : Genealogy.GenealogyNode
consentEngineeringTechnique = Genealogy.genealogyNode "consent-engineering / counter-mobilization technique" Genealogy.technique

wellnessConspirituality : Genealogy.GenealogyNode
wellnessConspirituality = Genealogy.genealogyNode "bounded conspirituality / wellness milieu" Genealogy.community

antiVaxNarrative : Genealogy.GenealogyNode
antiVaxNarrative = Genealogy.genealogyNode "anti-vaccination narrative/content" Genealogy.narrative

tradwifeAesthetic : Genealogy.GenealogyNode
tradwifeAesthetic = Genealogy.genealogyNode "tradwife / domesticity aesthetic" Genealogy.community

altRightNetwork : Genealogy.GenealogyNode
altRightNetwork = Genealogy.genealogyNode "alt-right / far-right network" Genealogy.community

------------------------------------------------------------------------
-- Grade A: direct archival/documented method transfer into food R&D.
------------------------------------------------------------------------

tobaccoToFoodTransfer : Genealogy.EvidenceEdge
tobaccoToFoodTransfer =
  Genealogy.evidenceEdge
    tobaccoIndustry
    ultraprocessedFoodRAndD
    Genealogy.directDocumentedTransfer
    Genealogy.gradeA
    (Sources.philipMorrisLunchablesPrimary ∷ [])
    "bounded Philip Morris tobacco-to-food R&D transfer documented in the cited internal-document case study; no universal food-industry genealogy is inferred"

tobaccoToFoodIsStrong : Genealogy.StrongEvidenceEdge tobaccoToFoodTransfer
tobaccoToFoodIsStrong = Genealogy.strongEvidenceEdge Genealogy.strongA

------------------------------------------------------------------------
-- Grade B: recurring personnel/strategy genealogy across tobacco and climate
-- doubt, as documented historically by Oreskes and Conway.  B rather than A
-- is deliberate: this is not encoded as one corporation directly transferring
-- one named internal technique into one named climate campaign.
------------------------------------------------------------------------

tobaccoToClimateHistoricalContinuity : Genealogy.EvidenceEdge
tobaccoToClimateHistoricalContinuity =
  Genealogy.evidenceEdge
    tobaccoIndustry
    climateDenialCampaigns
    Genealogy.personnelInstitutionalContinuity
    Genealogy.gradeB
    (Sources.merchantsOfDoubtHistory
      ∷ Sources.oreskesConwayNatureCommentary
      ∷ [])
    "historical continuity of recurring actors and doubt-production strategies across tobacco and climate controversies; does not establish central command"

tobaccoToClimateIsStrong :
  Genealogy.StrongEvidenceEdge tobaccoToClimateHistoricalContinuity
tobaccoToClimateIsStrong = Genealogy.strongEvidenceEdge Genealogy.strongB

------------------------------------------------------------------------
-- Grade A bounded organizational case: tobacco-backed counter-mobilization.
------------------------------------------------------------------------

tobaccoToNationalSmokersAlliance : Genealogy.EvidenceEdge
tobaccoToNationalSmokersAlliance =
  Genealogy.evidenceEdge
    tobaccoIndustry
    nationalSmokersAlliance
    Genealogy.fundingOrganisationalLink
    Genealogy.gradeA
    (Sources.nationalSmokersAllianceSource ∷ [])
    "bounded historical National Smokers Alliance case; no generic claim that every grassroots-looking organization is an industry front"

tobaccoToNationalSmokersAllianceIsStrong :
  Genealogy.StrongEvidenceEdge tobaccoToNationalSmokersAlliance
tobaccoToNationalSmokersAllianceIsStrong =
  Genealogy.strongEvidenceEdge Genealogy.strongA

------------------------------------------------------------------------
-- Grade C: bounded content/community adjacency.  Parmigiani's ethnographic
-- case is evidence of cross-domain circulation in a particular setting, not a
-- causal radicalisation theorem and not a population prevalence estimate.
------------------------------------------------------------------------

wellnessToAntiVaxAdjacency : Genealogy.EvidenceEdge
wellnessToAntiVaxAdjacency =
  Genealogy.evidenceEdge
    wellnessConspirituality
    antiVaxNarrative
    Genealogy.audienceContentAdjacency
    Genealogy.gradeC
    (Sources.conspiritualitySource ∷ [])
    "bounded ethnographic/content adjacency; does not establish wellness -> antivax causation or far-right radicalisation"

wellnessAdjacencyIsNotStrongHistoricalTransfer :
  Genealogy.StrongEvidenceEdge wellnessToAntiVaxAdjacency → ⊥
wellnessAdjacencyIsNotStrongHistoricalTransfer strong =
  Genealogy.gradeCIsNotStrong (Genealogy.gradeStrong strong)

------------------------------------------------------------------------
-- Tradwife -> alt-right is retained as a research candidate only in this
-- tranche: no source is installed here that would justify constructing an
-- EvidenceEdge, still less a StrongEvidenceEdge.
------------------------------------------------------------------------

record CandidateConnection : Set where
  constructor candidateConnection
  field
    source target : Genealogy.GenealogyNode

tradwifeToAltRightCandidate : CandidateConnection
tradwifeToAltRightCandidate = candidateConnection tradwifeAesthetic altRightNetwork

data CandidateConnectionPromotesToStrongGenealogy : Set where

candidateConnectionDoesNotPromoteWithoutReceipt :
  CandidateConnectionPromotesToStrongGenealogy → ⊥
candidateConnectionDoesNotPromoteWithoutReceipt ()

------------------------------------------------------------------------
-- Exact comparison: strong genealogy and bounded adjacency inhabit distinct
-- proof surfaces even when prose might call both a "pipeline".
------------------------------------------------------------------------

record CaseComparisonBoundary : Set where
  constructor caseComparisonBoundary
  field
    tobaccoFoodHasDirectTransferWitness : Bool
    tobaccoClimateHasStrongHistoricalContinuityWitness : Bool
    wellnessAntiVaxHasOnlyBoundedAdjacencyHere : Bool
    tradwifeAltRightStrongEdgeConstructedHere : Bool
    allNamedCasesAreOnePipeline : Bool

canonicalCaseComparisonBoundary : CaseComparisonBoundary
canonicalCaseComparisonBoundary =
  caseComparisonBoundary true true true false false
