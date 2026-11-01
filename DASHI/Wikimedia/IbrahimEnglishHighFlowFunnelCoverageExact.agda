module DASHI.Wikimedia.IbrahimEnglishHighFlowFunnelCoverageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- IBRAHIM ENGLISH HIGH-FLOW FUNNEL COVERAGE AUDIT
--
-- Method source:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI: 10.1016/j.jocs.2016.12.001
--
-- Ibrahim et al. report high-flow English first-link funnels around broad
-- concepts including Community, State, Science and Philosophy, with topical
-- accumulation around Health Care and Fossil Fuel.  We use those published
-- graph results as an external navigation prior for DASHI coverage auditing.
--
-- Current external identity coordinates checked 2026-09-10:
-- Community Q177634; state Q7275; science Q336; health care Q31207;
-- fossil fuel Q12748; philosophy Q5891.
--
-- The coverage classifications below are repository introspection results,
-- not Wikipedia theorem dependencies and not claims that current EN edges are
-- identical to the historical Ibrahim snapshot.
------------------------------------------------------------------------

data FunnelCoverageShape : Set where
  canonicalDomainStrong : FunnelCoverageShape
  strongDomainUnevenBreadth : FunnelCoverageShape
  strongSubstrateMissingCanonicalParent : FunnelCoverageShape
  fragmentedParentBridgeDebt : FunnelCoverageShape

record IbrahimFunnelProbe : Set where
  constructor ibrahim-funnel-probe
  field
    title : String
    qid : String
    publishedFunnelRole : String
    coverageShape : FunnelCoverageShape
    canonicalOwnerObserved : Bool
    reusableSubstrateObserved : Bool
    repositoryEvidence : String
    residual : String
open IbrahimFunnelProbe public

communityProbe : IbrahimFunnelProbe
communityProbe =
  ibrahim-funnel-probe
    "Community" "Q177634"
    "high-flow English first-link funnel in Ibrahim et al."
    fragmentedParentBridgeDebt
    false true
    "Education/CommunityConnectednessTopologyExact; culture, Indigenous-knowledge, governance, institutional-choice, social-ecology and community-observation surfaces"
    "consolidate a source-bounded Community parent bridge across social unit, place, shared practice, institutions and identity without collapsing distinct communities into one observer"

stateProbe : IbrahimFunnelProbe
stateProbe =
  ibrahim-funnel-probe
    "State" "Q7275"
    "high-flow English first-link funnel in Ibrahim et al."
    strongSubstrateMissingCanonicalParent
    false true
    "Governance/*, SensibLaw, Mabo/sovereignty, constitutional/jurisdictional and political-science/politics bridge surfaces"
    "add a canonical polity/state bridge distinguishing state, government, sovereignty, jurisdiction, territory and population; reuse existing law/governance owners"

scienceProbe : IbrahimFunnelProbe
scienceProbe =
  ibrahim-funnel-probe
    "Science" "Q336"
    "high-flow English first-link funnel in Ibrahim et al."
    strongSubstrateMissingCanonicalParent
    false true
    "Physics/BoundaryScienceEverything; Reasoning/MultiObserverScienceQuotient; source diligence, experiment, provenance, formal science, natural science and social-science surfaces"
    "make the repo-wide Science parent explicit as a bridge over empirical method, formal method, source/provenance and observer plurality; do not equate science with physics"

healthCareProbe : IbrahimFunnelProbe
healthCareProbe =
  ibrahim-funnel-probe
    "Health care" "Q31207"
    "topical English traversal-funnel accumulation reported by Ibrahim et al."
    strongDomainUnevenBreadth
    true true
    "Governance/HealthcareEqualityInvariant; HealthcareAccessDistortion; HealthcareEqualityDestructionBridge; PublicEssentialCareDoctrineBoundary plus biology/medicine-adjacent application surfaces"
    "health-care access/governance is strong; broaden explicit clinical delivery, professions, diagnosis/treatment/public-health bridges only where existing medical/biology owners do not already pay them"

fossilFuelProbe : IbrahimFunnelProbe
fossilFuelProbe =
  ibrahim-funnel-probe
    "Fossil fuel" "Q12748"
    "topical English traversal-funnel accumulation reported by Ibrahim et al."
    canonicalDomainStrong
    true true
    "Biology/DeepTimeCarbonBiosphereFossilFuelBidiExact; Chemistry/DeepTimeCarbonReservoirFluxBalanceExact; petroleum/refining/petrochemistry, climate and industrial-return joins"
    "retain as a strong bridge anchor; remaining debt is breadth across extraction, reserves, markets, infrastructure and policy rather than fossil-fuel formation itself"

philosophyProbe : IbrahimFunnelProbe
philosophyProbe =
  ibrahim-funnel-probe
    "Philosophy" "Q5891"
    "dominant English first-link traversal funnel in Ibrahim et al."
    canonicalDomainStrong
    true true
    "DASHI/Philosophy/Everything.agda, StableCore, BreadthProfile, RelationalAtlas, PowerAndGrammar, closure/context/valuation/repair owners"
    "use Philosophy as a strong terminal comparison anchor, but never infer that DASHI concepts are philosophically grounded merely because an EN traversal reaches Philosophy"

------------------------------------------------------------------------
-- Priority after quotienting existing content.
------------------------------------------------------------------------

record HighFlowResidualPriority : Set where
  constructor high-flow-residual-priority
  field
    communityParentBridgePriority : Bool
    stateParentBridgePriority : Bool
    scienceParentBridgePriority : Bool
    healthCareNeedsNewDomainFromZero : Bool
    fossilFuelNeedsNewDomainFromZero : Bool
    philosophyNeedsNewDomainFromZero : Bool
    strongestImmediateSharedParentDebt : String
open HighFlowResidualPriority public

currentHighFlowPriority : HighFlowResidualPriority
currentHighFlowPriority =
  high-flow-residual-priority
    true true true false false false
    "Community + State + Science parent consolidation; then use those funnels to audit social-science, archaeology/history, health, engineering and climate/economy cross-links"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data IbrahimFunnelCreatesDashiAuthority : Set where
data HighTraversalCountMeansFoundationalTruth : Set where
data PhilosophyReachabilityCreatesPhilosophicalGrounding : Set where
data ExistingLeafStringsPayCanonicalParent : Set where

ibrahimFunnelDoesNotCreateDashiAuthority : IbrahimFunnelCreatesDashiAuthority → ⊥
ibrahimFunnelDoesNotCreateDashiAuthority ()

traversalCountDoesNotCreateTruth : HighTraversalCountMeansFoundationalTruth → ⊥
traversalCountDoesNotCreateTruth ()

philosophyReachabilityDoesNotCreateGrounding : PhilosophyReachabilityCreatesPhilosophicalGrounding → ⊥
philosophyReachabilityDoesNotCreateGrounding ()

leafMentionsDoNotPayParent : ExistingLeafStringsPayCanonicalParent → ⊥
leafMentionsDoNotPayParent ()

record IbrahimHighFlowCoverageBoundary : Set where
  constructor ibrahim-high-flow-coverage-boundary
  field
    publishedGraphUsedAsNavigationPrior : Bool
    qidsUsedAsExternalIdentityCoordinates : Bool
    repositorySubstrateReused : Bool
    parentDebtSeparatedFromLeafDepth : Bool
    wikipediaCentralityCreatesFormalAuthority : Bool
open IbrahimHighFlowCoverageBoundary public

canonicalIbrahimHighFlowCoverageBoundary : IbrahimHighFlowCoverageBoundary
canonicalIbrahimHighFlowCoverageBoundary =
  ibrahim-high-flow-coverage-boundary true true true true false
