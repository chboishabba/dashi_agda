module DASHI.Finance.TrumpFamilyPolicyMarketSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Trade

------------------------------------------------------------------------
-- POLICY / MARKET EXPOSURE SOURCE ATLAS
--
-- Ownership evidence, policy text, market-information products and claims about
-- knowledge/influence are separate propositions.  Two canonical fixtures are
-- retained:
--
-- GrabAGun:
-- 1. SEC ownership/board evidence already acquired by the trade atlas;
-- 2. ATF RIN 1140-AB05 primary proposed-rule text (2026-05-08; no DOI);
-- 3. Reuters independent report (2026-07-02; no DOI), including attributed
--    statements concerning prior knowledge/influence.
--
-- Truth API:
-- 1. TMTG's SEC-filed issuer exhibit describing low-latency access to public
--    Truth Social posts and HFT/algorithmic-firm target customers;
-- 2. Reuters independent reporting on proposed commercial pricing/market use;
-- 3. the Schiff/Warren request that the SEC investigate, retained as an
--    attributed regulatory concern rather than an adjudicated finding.
------------------------------------------------------------------------

data PolicyMarketEvidenceKind : Set where
  policyProposalPrimary : PolicyMarketEvidenceKind
  independentPolicyMarketSynthesis : PolicyMarketEvidenceKind

data PolicyMarketSupportMode : Set where
  directAgencyText : PolicyMarketSupportMode
  independentReportingWithAttributedStatements : PolicyMarketSupportMode

record PolicyMarketEvidence : Set₁ where
  constructor policyMarketEvidence
  field
    evidenceId : String
    subject : String
    proposition : String
    supportMode : PolicyMarketSupportMode
    source : Source.SourceArtifact
    sourceTitle : String
    sourceAuthor : String
    sourceDate : String
    doi : String
    supportScope : String
    primarySourcePaid : Bool
    independentCorroborationPaid : Bool
    knowledgeClaimPaid : Bool
    influenceClaimPaid : Bool
    realizedBenefitPaid : Bool

open PolicyMarketEvidence public

grabAGunATFArtifact : Source.SourceArtifact
grabAGunATFArtifact = Source.sourceArtifact
  "ATF-RIN-1140-AB05-2026-05-08"
  Source.documentaryArtifact
  "https://www.atf.gov/rules-and-regulations/rulemaking-notices/revising-non-over-counter-firearms-transaction-requirements-rin-1140-ab05"
  "Bureau of Alcohol, Tobacco, Firearms and Explosives"

grabAGunATFNonOTCProposal : PolicyMarketEvidence
grabAGunATFNonOTCProposal = policyMarketEvidence
  "GrabAGun-policy-ATF-NOTC-2026"
  "ATF proposed rule / online-first firearm retailers"
  "ATF proposed amending non-over-the-counter firearm-sale regulations to permit same-state FFL transfers without in-person appearance while retaining background-check requirements and adding remote identity proofing and electronic law-enforcement notice."
  directAgencyText
  grabAGunATFArtifact
  "Revising Non-Over-the-Counter Firearms Transaction Requirements (RIN 1140-AB05)"
  "Bureau of Alcohol, Tobacco, Firearms and Explosives"
  "2026-05-08" "no DOI"
  "Supports the existence, scope and stated purpose of the proposed rule only. It does not identify beneficiaries, knowledge, influence, motive or realized market impact."
  true false false false false

grabAGunReutersArtifact : Source.SourceArtifact
grabAGunReutersArtifact = Source.sourceArtifact
  "Reuters-2026-07-02-GrabAGun-policy-exposure"
  Source.documentaryArtifact
  "https://www.reuters.com/legal/government/trump-jrs-amazon-guns-could-make-millions-under-new-proposed-firearm-rule-2026-07-02/"
  "Reuters"

grabAGunReutersPolicyExposure : PolicyMarketEvidence
grabAGunReutersPolicyExposure = policyMarketEvidence
  "GrabAGun-policy-Reuters-2026-07-02"
  "Donald J. Trump Jr. / GrabAGun / ATF proposed rule"
  "Reuters reported that the proposed ATF rule could materially expand the addressable market for online-first firearms retailers including GrabAGun; it also reported attributed statements that Trump Jr. had no role in the proposal, that GrabAGun's CEO said neither he nor Trump Jr. knew it was coming, that ATF chief counsel Robert Leider said he was unaware of Trump Jr.'s GrabAGun connection until Reuters asked, and that the White House said it had no record or knowledge of interactions with the president's son on those topics."
  independentReportingWithAttributedStatements
  grabAGunReutersArtifact
  "Trump Jr.'s 'Amazon of guns' could make millions under new proposed firearm rule"
  "Reuters"
  "2026-07-02" "no DOI"
  "Supports independent reporting on structural business exposure and the existence/content of attributed denials/statements. It does not prove absence of knowledge or influence, realized profit, illegality, or policy causation."
  false true false false false

record GrabAGunKnowledgeBoundary : Set where
  constructor grabAGunKnowledgeBoundaryRecord
  field
    ownershipAndBoardRolePaid : Bool
    proposedPolicyPaid : Bool
    independentExposureAnalysisPaid : Bool
    attributedNoPriorKnowledgeStatementsRetained : Bool
    priorKnowledgeAffirmativelyEstablished : Bool
    policyInfluenceEstablished : Bool
    realizedWindfallEstablished : Bool
    attributedDenialsProveUniversalNegative : Bool

open GrabAGunKnowledgeBoundary public

grabAGunKnowledgeBoundary : GrabAGunKnowledgeBoundary
grabAGunKnowledgeBoundary =
  grabAGunKnowledgeBoundaryRecord true true true true false false false false

record PolicyMarketTriad : Set₁ where
  constructor policyMarketTriad
  field
    ownershipEvidence : Trade.TradeEvidenceClaim
    policyEvidence : PolicyMarketEvidence
    independentEvidence : PolicyMarketEvidence
    knowledgeBoundary : GrabAGunKnowledgeBoundary
    ownershipSourceIsPrimary : Trade.primarySourcePaid ownershipEvidence ≡ true
    policySourceIsPrimary : primarySourcePaid policyEvidence ≡ true
    independentSourceIsIndependent : independentCorroborationPaid independentEvidence ≡ true
    triadReference : String

open PolicyMarketTriad public

canonicalGrabAGunPolicyMarketTriad : PolicyMarketTriad
canonicalGrabAGunPolicyMarketTriad = policyMarketTriad
  Trade.donJrGrabAGunVesting
  grabAGunATFNonOTCProposal
  grabAGunReutersPolicyExposure
  grabAGunKnowledgeBoundary
  refl refl refl
  "SEC ownership/role + ATF proposed-rule text + Reuters independent exposure/counterevidence synthesis; knowledge, influence and realized benefit remain unpaid."

------------------------------------------------------------------------
-- Truth API: information-latency monetisation is a market-structure edge, not
-- evidence of material nonpublic information or a securities-law violation.
------------------------------------------------------------------------

truthAPIReutersArtifact : Source.SourceArtifact
truthAPIReutersArtifact = Source.sourceArtifact
  "Reuters-2026-07-17-Truth-API-market-access"
  Source.documentaryArtifact
  "https://www.reuters.com/business/media-telecom/trump-media-pitched-100000-monthly-fee-fast-feed-us-presidents-posts-ft-reports-2026-07-17/"
  "Reuters"

truthAPIReutersMarketAccess : PolicyMarketEvidence
truthAPIReutersMarketAccess = policyMarketEvidence
  "Truth-API-Reuters-2026-07-17"
  "Trump Media & Technology Group / Truth API"
  "Reuters reported that Trump Media had pitched institutional customers a high-priced low-latency feed for Truth Social posts, with proposed monthly pricing up to $100,000 and a lower long-term-commitment price; the report framed the service as faster access to public posts for traders."
  independentReportingWithAttributedStatements
  truthAPIReutersArtifact
  "Trump Media pitched $100,000 monthly fee for fastest feed of US president's posts, sources say"
  "Reuters"
  "2026-07-17" "no DOI"
  "Supports independent reporting on proposed commercial terms and market-access design. It does not establish MNPI, trading profit, illegality, policy influence or a particular customer's use."
  false true false false false

record TruthAPIPolicyMarketTriad : Set₁ where
  constructor truth-api-policy-market-triad
  field
    issuerProductEvidence : Trade.TradeEvidenceClaim
    independentMarketEvidence : PolicyMarketEvidence
    attributedRegulatoryConcern : Trade.TradeEvidenceClaim
    issuerProductPrimaryPaid : Trade.primarySourcePaid issuerProductEvidence ≡ true
    independentMarketCorroborationPaid : independentCorroborationPaid independentMarketEvidence ≡ true
    regulatoryConcernIsAttributed : Trade.supportMode attributedRegulatoryConcern ≡ Trade.attributedConcernSupport
    materialNonpublicInformationPaid : Bool
    legalViolationPaid : Bool
    profitableTradingStrategyPaid : Bool
    triadReference : String

open TruthAPIPolicyMarketTriad public

canonicalTruthAPIPolicyMarketTriad : TruthAPIPolicyMarketTriad
canonicalTruthAPIPolicyMarketTriad = truth-api-policy-market-triad
  Trade.truthAPIPrimary
  truthAPIReutersMarketAccess
  Trade.truthAPIRegulatoryConcern
  refl refl refl
  false false false
  "SEC-filed issuer product disclosure + Reuters market-access synthesis + attributed Schiff/Warren SEC-investigation request; MNPI, legal violation and profitable strategy remain unpaid."

record PolicyMarketAtlasBoundary : Set where
  constructor policy-market-atlas-boundary
  field
    ownershipDoesNotEqualPolicyInfluence : Bool
    policyExposureDoesNotEqualRealizedBenefit : Bool
    denialDoesNotEqualProvedAbsence : Bool
    timingDoesNotEqualCausation : Bool
    lowLatencyPublicFeedDoesNotEqualMNPI : Bool
    investigationRequestDoesNotEqualViolation : Bool
    sourceTriangulationCanReduceEvidenceDebt : Bool

canonicalPolicyMarketAtlasBoundary : PolicyMarketAtlasBoundary
canonicalPolicyMarketAtlasBoundary =
  policy-market-atlas-boundary true true true true true true true
