module DASHI.Cognition.PalantirTIAFinanceStateCapacityCrossPollination20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.Project2025PalantirImmigrationDataIntersectionExact as Immigration
import DASHI.Cognition.MavenMinabPineGapTargetingChainExact as Maven
import DASHI.Cognition.EpsteinThielValarDirectSolicitation20261014Exact as ThielValar
import DASHI.Cognition.SystemicLeverageBeneficiaryIncidenceParetoExact as Incidence
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Capability
import DASHI.Governance.PalantirProcurementLegibilityAdapterExact as Procurement

------------------------------------------------------------------------
-- PALANTIR TIA x FINANCE x STATE-CAPACITY CROSS-POLLINATION — 2026-10-15
--
-- Recent sibling PR #1161 (head observed: 223d3407006de2c22f9b17a7c87fbcac7d415fa5)
-- source-writes a Palantir/TIA genealogy and party-distribution/Pareto layer.
-- This owner does NOT import that unmerged sibling as theorem authority.
-- Instead it records the bounded donor propositions and composes them with
-- same-branch owners already paying modern Palantir deployments and the
-- independently paid Epstein -> Thiel/Valar finance path.
--
-- Governing non-collapse:
--   shared person != shared capital
--   historical genealogy != programme identity
--   capability continuity != asset/code transfer
--   investment/customer access != procurement authority
--   procurement != policy authorship
--   installed base != lock-in unless renewal/exit evidence pays it
------------------------------------------------------------------------

data Stage : Set where
  publicResearchProgramme : Stage
  statutoryDisposition : Stage
  intelligenceCapitalCustomerAccess : Stage
  vendorProductDevelopment : Stage
  operationalProcurement : Stage
  policyCapabilityIntersection : Stage
  durableStateCapacity : Stage
  institutionalLockInCandidate : Stage

record StageReceipt : Set where
  constructor stage-receipt
  field
    label : String
    stage : Stage
    source : String
    boundedFinding : String
    paid : Bool
    sameProgrammeIdentityPaid : Bool
    directCausalContinuityPaid : Bool
open StageReceipt public

tiaProgrammeReceipt : StageReceipt
tiaProgrammeReceipt = stage-receipt
  "TIA programme and congressional disposition"
  statutoryDisposition
  "Observed sibling PR #1161 source atlas: 2003 Congressional Record / Public Law 108-87 / Senate Intelligence conference report"
  "TIA/IAO and its statutory termination/disposition are source-paid in the sibling genealogy. Congress also treated related/successor/transferred components as a distinct continuity concern. This pays a historical programme/disposition coordinate, not Palantir identity."
  true false false

poindexterThielKarpReceipt : StageReceipt
poindexterThielKarpReceipt = stage-receipt
  "Poindexter meeting with Karp/Thiel"
  intelligenceCapitalCustomerAccess
  "Observed sibling PR #1161 source atlas: Wired 'Joining the Dots' reporting Poindexter's account"
  "The sibling source surface records Poindexter's account of Alex Karp and Peter Thiel meeting him at Richard Perle's home and discussing a Palantir/TIA-like analytics problem. This pays contact/context, not programme succession or code transfer."
  true false false

iqtCIADevelopmentReceipt : StageReceipt
iqtCIADevelopmentReceipt = stage-receipt
  "In-Q-Tel / early CIA-facing Palantir development"
  intelligenceCapitalCustomerAccess
  "Observed sibling PR #1161: In-Q-Tel portfolio + attributed early CIA-facing development history"
  "Palantir's early history includes In-Q-Tel investment/customer access and CIA-facing development/feedback. This pays capital/customer-access and product-development coordinates; investment does not equal procurement sovereignty or TIA continuity."
  true false false

iceDeploymentReceipt : StageReceipt
iceDeploymentReceipt = stage-receipt
  "ICE Palantir ICM/ImmigrationOS/ERO deployment"
  operationalProcurement
  "Project2025PalantirImmigrationDataIntersectionExact"
  "The active branch independently pays long-running ICE Palantir case-management/data capability, ImmigrationOS targeting/support functions and the 2026 ERO-related award."
  true false false

mavenDeploymentReceipt : StageReceipt
mavenDeploymentReceipt = stage-receipt
  "Maven / Palantir military-AI deployment"
  operationalProcurement
  "MavenMinabPineGapTargetingChainExact"
  "The active branch independently pays Palantir's Maven expansion/core-program role and source-attributed 2026 Iran targeting use, while blocking sole-machine-cause and specific Pine-Gap-datum promotion."
  true false false

project2025IntersectionReceipt : StageReceipt
project2025IntersectionReceipt = stage-receipt
  "Project 2025 data-integration demand x Palantir capability"
  policyCapabilityIntersection
  "Project2025PalantirImmigrationDataIntersectionExact"
  "Policy demand for integrated enforcement/data capacity and actual Palantir procurement are separately paid. Their intersection is valid for incidence analysis but does not establish vendor-selection causation."
  true false false

------------------------------------------------------------------------
-- Repo-native capability / legibility grammar.
------------------------------------------------------------------------

record OperationalGrammarBoundary : Set where
  constructor operational-grammar-boundary
  field
    objectPropertyLinkGraphPaid : Bool
    operationalActionLayerPaid : Bool
    granularPermissioningPaid : Bool
    auditLoggingPaid : Bool
    procurementEvidencePaid : Bool
    deploymentSubjectDataReceiptPaid : Bool
    deploymentDecisionUseReceiptPaid : Bool
    subjectInspectionCorrectionAppealPaid : Bool
    genericCapabilityCreatesDeploymentAsymmetry : Bool
    procurementCreatesLegibilityWitness : Bool
    historicalGenealogyCreatesDeploymentReceipt : Bool
open OperationalGrammarBoundary public

canonicalOperationalGrammarBoundary : OperationalGrammarBoundary
canonicalOperationalGrammarBoundary = operational-grammar-boundary
  true true true true true false false false false false false

data HistoricalGenealogyImpliesDeploymentReceipt : Set where
data GenericCapabilityImpliesSubjectAsymmetry : Set where
data ProcurementImpliesSubjectContestability : Set where

historicalGenealogyDoesNotCreateDeploymentReceipt : HistoricalGenealogyImpliesDeploymentReceipt → ⊥
historicalGenealogyDoesNotCreateDeploymentReceipt ()

genericCapabilityDoesNotCreateSubjectAsymmetry : GenericCapabilityImpliesSubjectAsymmetry → ⊥
genericCapabilityDoesNotCreateSubjectAsymmetry ()

procurementDoesNotCreateSubjectContestability : ProcurementImpliesSubjectContestability → ⊥
procurementDoesNotCreateSubjectContestability ()

------------------------------------------------------------------------
-- Shared-Thiel cross-pollination into the Epstein/Valar financial graph.
------------------------------------------------------------------------

record SharedPersonBridge : Set where
  constructor shared-person-bridge
  field
    person : String
    leftSurface : String
    rightSurface : String
    samePersonPaid : Bool
    capitalTransferredBetweenSurfacesPaid : Bool
    palantirInvestmentByEpsteinPaid : Bool
    commonCommandPaid : Bool
open SharedPersonBridge public

thielBridge : SharedPersonBridge
thielBridge = shared-person-bridge
  "Peter Thiel"
  "direct 2014 Thiel -> Epstein Valar solicitation; Southern Trust later Valar II/III LP"
  "Palantir co-founder / early Palantir-In-Q-Tel-CIA development context observed in sibling PR #1161"
  true false false false

data SharedPersonImpliesSharedCapital : Set where
data ValarInvestmentImpliesPalantirInvestment : Set where
data TIAContextImpliesEpsteinPalantirOperation : Set where

sharedPersonDoesNotCreateSharedCapital : SharedPersonImpliesSharedCapital → ⊥
sharedPersonDoesNotCreateSharedCapital ()

valarDoesNotCreatePalantirInvestment : ValarInvestmentImpliesPalantirInvestment → ⊥
valarDoesNotCreatePalantirInvestment ()

tiaContextDoesNotCreateEpsteinPalantirOperation : TIAContextImpliesEpsteinPalantirOperation → ⊥
tiaContextDoesNotCreateEpsteinPalantirOperation ()

------------------------------------------------------------------------
-- Stage-preserving systemic chain.
------------------------------------------------------------------------

record StateCapacityChain : Set where
  constructor state-capacity-chain
  field
    historicalProgrammePaid : Bool
    historicalDispositionPaid : Bool
    earlyCapitalCustomerAccessPaid : Bool
    genericPlatformCapabilityPaid : Bool
    modernOperationalProcurementPaid : Bool
    policyCapabilityIntersectionPaid : Bool
    sameProgrammeIdentityPaid : Bool
    assetOrCodeTransferPaid : Bool
    personnelAuthorityContinuityPaid : Bool
    procurementScopeContinuityPaid : Bool
    institutionalDecisionAuthorityContinuityPaid : Bool
    durableCapacityWorthInvestigating : Bool
    lockInAlreadyProved : Bool
open StateCapacityChain public

canonicalStateCapacityChain : StateCapacityChain
canonicalStateCapacityChain = state-capacity-chain
  true true true true true true
  false false false false false
  true false

------------------------------------------------------------------------
-- First / second / third order incidence adapter.
------------------------------------------------------------------------

palantirHistoricalToOperationalFirstOrder : Incidence.SystemicLeverageCandidate
palantirHistoricalToOperationalFirstOrder = Incidence.systemic-leverage-candidate
  "Palantir historical capital/customer access -> modern operational procurement"
  Incidence.firstOrder
  Incidence.procurementContracting
  "Which early capital/customer-access advantages became product capability that later won specific government procurements?"
  "Vendor gains revenue, deployment experience, customer feedback and installed product position; customers gain operational analytics capability."
  "Public funding, delivery risk, privacy/error burdens and competitive displacement require deployment-specific measurement."
  "Separate investor/customer access, vendor implementation authority, procurement authority and policy authority on each object."
  "In-Q-Tel terms; early CIA development records; contract statements of work; renewals; product/version lineage"
  true false false

palantirInstalledBaseSecondOrder : Incidence.SystemicLeverageCandidate
palantirInstalledBaseSecondOrder = Incidence.systemic-leverage-candidate
  "Palantir installed-base / switching-cost hypothesis"
  Incidence.secondOrder
  Incidence.exitConstraint
  "Do repeated Palantir deployments create switching costs, data/schema dependence, renewal advantage or cross-program reuse?"
  "Incumbent vendor and customer operators may gain continuity and option value if integrations are reusable."
  "Competitors, oversight bodies and affected subjects may bear exit/contestability burdens if schemas, workflows or audit surfaces are difficult to migrate."
  "Who owns schemas/configuration, export tooling, derived models, audit history and migration rights?"
  "renewal history; interoperability/export clauses; migration attempts; sole/limited-source justifications; architecture records"
  false false false

palantirStateCapacityThirdOrder : Incidence.SystemicLeverageCandidate
palantirStateCapacityThirdOrder = Incidence.systemic-leverage-candidate
  "Palantir-enabled durable state-capacity hypothesis"
  Incidence.thirdOrder
  Incidence.institutionalControl
  "Do independently procured analytics/data systems persist across programmes and administrations in ways that expand durable classification/targeting/enforcement capacity?"
  "Successor agencies/administrations and incumbent vendors may inherit technical capacity beyond the initiating policy coalition."
  "Long-run burdens may include mission expansion, propagated classification errors, reduced practical contestability or institutional path dependence; each needs evidence."
  "Distinguish vendor capability, customer operational authority, statutory authority, policy authorship and subject remedy."
  "longitudinal deployment records; successor contracts; decommissioning/migration evidence; audits; litigation; correction/remedy records"
  false false false

------------------------------------------------------------------------
-- Sibling provenance boundary.
------------------------------------------------------------------------

record SiblingDonorReceipt : Set where
  constructor sibling-donor-receipt
  field
    pr : String
    observedHead : String
    observedFiles : String
    externalSourcesRetainOwnAuthority : Bool
    siblingTheoremAuthorityImported : Bool
    boundedPropositionsReconstructedLocally : Bool
open SiblingDonorReceipt public

palantirTIASibling : SiblingDonorReceipt
palantirTIASibling = sibling-donor-receipt
  "dashi_agda PR #1161"
  "223d3407006de2c22f9b17a7c87fbcac7d415fa5"
  "PalantirTIAHistoricalGenealogyExact; PalantirTIAInvestigativeParetoSnowballExact; PalantirTIAPartyBenefitDistributionExact"
  true false true

------------------------------------------------------------------------
-- Max-cut acquisition after cross-pollination.
------------------------------------------------------------------------

data PalantirCrossDebt : Set where
  earlyIQTInvestmentTerms : PalantirCrossDebt
  earlyCIADevelopmentObjects : PalantirCrossDebt
  tiaSuccessorComponentIdentity : PalantirCrossDebt
  personnelAssetRequirementTransfer : PalantirCrossDebt
  procurementRenewalInstalledBase : PalantirCrossDebt
  schemaDataModelExitRights : PalantirCrossDebt
  thielEpsteinPalantirSpecificEdge : PalantirCrossDebt
  subjectContestabilitySameDeployment : PalantirCrossDebt

record PalantirCrossAcquisition : Set where
  constructor palantir-cross-acquisition
  field
    debt : PalantirCrossDebt
    priority : Nat
    sameObjectRequired : Bool
    instruction : String
open PalantirCrossAcquisition public

canonicalPalantirCrossAcquisition : List PalantirCrossAcquisition
canonicalPalantirCrossAcquisition =
  palantir-cross-acquisition earlyIQTInvestmentTerms 100 true
    "Acquire contemporaneous In-Q-Tel investment terms, dates, participants and product/customer scope; current portfolio identity alone does not pay the original transaction mechanics."
  ∷ palantir-cross-acquisition earlyCIADevelopmentObjects 100 true
    "Resolve named early CIA development/customer objects, feedback loops and version/product scope to connect capital/customer access to concrete capability without calling it TIA succession."
  ∷ palantir-cross-acquisition tiaSuccessorComponentIdentity 100 true
    "Follow Public Law 108-87/Senate Intelligence disposition into declassified successor/component programme identities, custodians and funding; statutory continuation language does not identify Palantir."
  ∷ palantir-cross-acquisition procurementRenewalInstalledBase 99 true
    "Join ICE/Maven and other deployments to renewal/extension/limited-source records to measure installed-base persistence, contract revenue and switching advantage."
  ∷ palantir-cross-acquisition schemaDataModelExitRights 99 true
    "Acquire export/interoperability/configuration/data-model ownership and migration clauses to test lock-in rather than infer it from repeated procurement."
  ∷ palantir-cross-acquisition personnelAssetRequirementTransfer 98 true
    "Search for same-person authority, code/asset or requirement transfer from TIA/IAO or successor components into Palantir-linked development; similarity alone remains insufficient."
  ∷ palantir-cross-acquisition thielEpsteinPalantirSpecificEdge 98 true
    "Search independently for any Epstein/Southern Trust -> Palantir investment, proposal, service, introduction or governance object. Thiel + Valar + Palantir does not create this edge transitively."
  ∷ palantir-cross-acquisition subjectContestabilitySameDeployment 97 true
    "Pair a concrete Palantir deployment with privacy/impact/audit/challenge/remedy records for affected subjects so benefit/burden/voice/authority are measured on the same object."
  ∷ []
