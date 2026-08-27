module DASHI.Governance.Kallis2025EvidenceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Governance.Kallis2025ClaimAuthorityRoutingExact as Routing
import DASHI.Governance.SafeJustSourceRegistryExact as Sources

------------------------------------------------------------------------
-- KALLIS ET AL. 2025: EVIDENCE ATLAS
--
-- Source: Giorgos Kallis et al.,
-- "Post-growth: the science of wellbeing within planetary boundaries",
-- Lancet Planetary Health 9 (2025), e62--e78,
-- DOI 10.1016/S2542-5196(24)00310-3.
--
-- This module records the review's major evidence clusters and selected
-- reference-number anchors.  It does not promote review prose into stronger
-- causal, predictive or normative authority than the cited source class.
------------------------------------------------------------------------

data EvidenceCluster : Set where
  resourceLimits
  planetaryBoundaries
  decoupling
  wellbeingAndGDP
  ecologicalMacroeconomics
  policyPackages
  growthDependencies
  provisioningSystems
  globalNorthSouthRelations
  politicsOfTransition
  : EvidenceCluster

data EvidenceClass : Set where
  empiricalCrossNational
  empiricalHistorical
  modelScenario
  modelReview
  caseStudy
  policyExperiment
  theoreticalSynthesis
  politicalEconomyAnalysis
  unresolvedResearchFrontier
  : EvidenceClass

record EvidenceAnchor : Set where
  constructor evidenceAnchor
  field
    cluster : EvidenceCluster
    evidenceClass : EvidenceClass
    reviewReference : Nat
    claimRole : Routing.ClaimRole

-- Selected literal anchors from the review's numbered bibliography.
-- They are representative routing points, not an exhaustive bibliography.
materialFootprintCoupling : EvidenceAnchor
materialFootprintCoupling =
  evidenceAnchor decoupling empiricalCrossNational 47 Routing.empiricalSynthesis

materialDecouplingReview : EvidenceAnchor
materialDecouplingReview =
  evidenceAnchor decoupling modelReview 48 Routing.empiricalSynthesis

optimisticTechnologyProjection : EvidenceAnchor
optimisticTechnologyProjection =
  evidenceAnchor decoupling modelScenario 49 Routing.empiricalSynthesis

postGrowthMitigationScenario : EvidenceAnchor
postGrowthMitigationScenario =
  evidenceAnchor decoupling modelScenario 66 Routing.empiricalSynthesis

lowGrowCanada : EvidenceAnchor
lowGrowCanada =
  evidenceAnchor ecologicalMacroeconomics modelScenario 126 Routing.empiricalSynthesis

eurogreenFrance : EvidenceAnchor
neurogreenFrance =
  evidenceAnchor ecologicalMacroeconomics modelScenario 127 Routing.empiricalSynthesis

policyPackageSynthesis : EvidenceAnchor
policyPackageSynthesis =
  evidenceAnchor policyPackages theoreticalSynthesis 139 Routing.empiricalSynthesis

workingTimeCarbonAssociation : EvidenceAnchor
workingTimeCarbonAssociation =
  evidenceAnchor policyPackages empiricalHistorical 129 Routing.empiricalSynthesis

provisioningSystemsOwner : EvidenceAnchor
provisioningSystemsOwner =
  evidenceAnchor provisioningSystems empiricalCrossNational 185 Routing.empiricalSynthesis

lowEnergyNeedSatisfactionOwner : EvidenceAnchor
lowEnergyNeedSatisfactionOwner =
  evidenceAnchor provisioningSystems empiricalCrossNational 186 Routing.empiricalSynthesis

unequalExchangeOwner : EvidenceAnchor
unequalExchangeOwner =
  evidenceAnchor globalNorthSouthRelations politicalEconomyAnalysis 190 Routing.empiricalSynthesis

gdp15000Owner : EvidenceAnchor
gdp15000Owner =
  evidenceAnchor wellbeingAndGDP empiricalCrossNational 98 Routing.empiricalRestatement

------------------------------------------------------------------------
-- Review-level frontier distinctions.
------------------------------------------------------------------------

data EvidenceStatus : Set where
  supportedContestedOpen : EvidenceStatus

record ClusterBoundary : Set where
  constructor clusterBoundary
  field
    cluster : EvidenceCluster
    reviewMaySynthesize : Bool
    reviewMaySynthesizeIsTrue : reviewMaySynthesize ≡ true
    synthesisAloneIdentifiesCausalMechanism : Bool
    synthesisAloneIdentifiesCausalMechanismIsFalse :
      synthesisAloneIdentifiesCausalMechanism ≡ false

canonicalProvisioningClusterBoundary : ClusterBoundary
canonicalProvisioningClusterBoundary =
  clusterBoundary provisioningSystems true refl false refl

canonicalDecouplingClusterBoundary : ClusterBoundary
canonicalDecouplingClusterBoundary =
  clusterBoundary decoupling true refl false refl

record KallisEvidenceAtlasBoundary : Set where
  constructor kallisEvidenceAtlasBoundary
  field
    allReviewClaimsShareOneEvidenceClass : Bool
    allReviewClaimsShareOneEvidenceClassIsFalse :
      allReviewClaimsShareOneEvidenceClass ≡ false
    modelScenarioEqualsHistoricalObservation : Bool
    modelScenarioEqualsHistoricalObservationIsFalse :
      modelScenarioEqualsHistoricalObservation ≡ false
    empiricalAssociationEqualsPolicyMandate : Bool
    empiricalAssociationEqualsPolicyMandateIsFalse :
      empiricalAssociationEqualsPolicyMandate ≡ false
    globalNorthSouthQuestionIsClosedByTheReview : Bool
    globalNorthSouthQuestionIsClosedByTheReviewIsFalse :
      globalNorthSouthQuestionIsClosedByTheReview ≡ false
    politicsOfTransitionIsClosedByTheReview : Bool
    politicsOfTransitionIsClosedByTheReviewIsFalse :
      politicsOfTransitionIsClosedByTheReview ≡ false

canonicalKallisEvidenceAtlasBoundary : KallisEvidenceAtlasBoundary
canonicalKallisEvidenceAtlasBoundary =
  kallisEvidenceAtlasBoundary false refl false refl false refl false refl false refl

source : Sources.SourceReference
source = Sources.kallis2025
