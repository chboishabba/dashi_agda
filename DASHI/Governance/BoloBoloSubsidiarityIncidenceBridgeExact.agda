module DASHI.Governance.BoloBoloSubsidiarityIncidenceBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Bolo
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base
import DASHI.Governance.FederatedDecisionIncidenceExact as Incidence
import DASHI.Governance.FederatedDecisionIncidenceFiniteExampleExact as Example

------------------------------------------------------------------------
-- BOLO'BOLO -> SUBSIDIARITY / INCIDENCE BRIDGE.
--
-- p.m.'s source supplies the nested design motivation.  The theorem itself is
-- a DASHI reuse of the already-existing generic subsidiarity result.  Nothing
-- here attributes DASHI's formal ontology or theorem statement to p.m.
------------------------------------------------------------------------

BoloLocalityContraction :
  ∀ {Agent Community Issue : Set} →
  Base.FederatedGovernance Agent Community Issue →
  Issue → Issue → Set₁
BoloLocalityContraction governance localIssue globalIssue =
  Incidence.StrictParticipationContraction governance localIssue globalIssue

boloNestedLocalityContraction :
  ∀ {Agent Community Issue : Set}
    {governance : Base.FederatedGovernance Agent Community Issue} →
  (sourceDesign : Bolo.BoloBoloPrimarySourceAtlas) →
  (subsidiarity : Base.SubsidiarityWitness governance) →
  ∀ {localIssue globalIssue community} →
  Base.scopeOf governance localIssue ≡ Base.localTo community →
  Σ Agent (λ agent → ¬ Base.memberOf governance agent community) →
  Incidence.GloballyCoupledIssue governance globalIssue →
  BoloLocalityContraction governance localIssue globalIssue
boloNestedLocalityContraction sourceDesign subsidiarity localScope outsider globalCoupling =
  Incidence.localToGlobalStrictParticipationContraction
    subsidiarity
    localScope
    outsider
    globalCoupling

------------------------------------------------------------------------
-- Existing finite specimen routed through the bolo bridge.
-- This remains synthetic and demonstrates theorem shape only.
------------------------------------------------------------------------

exampleBoloLocalityContraction :
  BoloLocalityContraction
    Example.exampleGovernance
    Example.localAIssue
    Example.federationIssue
exampleBoloLocalityContraction =
  boloNestedLocalityContraction
    Bolo.canonicalBoloBoloPrimarySourceAtlas
    Example.exampleSubsidiarity
    refl
    (Example.agentBOne , Example.agentBOneOutsideA)
    Example.exampleFederationCoupled

------------------------------------------------------------------------
-- Interpretation firewall.
------------------------------------------------------------------------

record BoloSubsidiarityBridgeBoundary : Set where
  constructor boloSubsidiarityBridgeBoundary
  field
    sourceProvidesNestedDesignMotivation : Bool
    sourceArchitectureEqualsFormalSubsidiarityOntology : Bool
    dashiContractionTheoremAttributedToPM : Bool
    localityContractionRequiresSubsidiarityAndOutsiderWitness : Bool
    globalComparisonRequiresSuppliedGlobalCoupling : Bool
    strictContractionIsEmpiricalCostReduction : Bool
    strictContractionProvesPoliticalLegitimacy : Bool
    strictContractionProvesEcologicalViability : Bool

open BoloSubsidiarityBridgeBoundary public

canonicalBoloSubsidiarityBridgeBoundary : BoloSubsidiarityBridgeBoundary
canonicalBoloSubsidiarityBridgeBoundary =
  boloSubsidiarityBridgeBoundary
    true
    false
    false
    true
    true
    false
    false
    false

canonicalBoloSubsidiarityIncidenceBridgeReceipt : GenericReceipt.GenericReceipt
canonicalBoloSubsidiarityIncidenceBridgeReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo nested-design to subsidiarity/incidence bridge"
    "DASHI.Governance.BoloBoloSubsidiarityIncidenceBridgeExact"
    "boloNestedLocalityContraction / canonicalBoloSubsidiarityBridgeBoundary"
    "uses p.m.'s nested design only as source motivation and reuses the existing DASHI theorem that a genuinely local issue with an outsider has a strictly contracted participant fibre relative to any supplied globally coupled comparison issue"
    "the bridge is conditional on explicit subsidiarity, outsider and global-coupling witnesses; strict participation contraction is not itself a measured coordination-cost reduction, legitimacy theorem, ecological result, or source-authored formalism"
    "agda -i . DASHI/Governance/BoloBoloSubsidiarityIncidenceBridgeRegression.agda"
