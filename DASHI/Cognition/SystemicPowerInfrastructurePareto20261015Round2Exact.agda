module DASHI.Cognition.SystemicPowerInfrastructurePareto20261015Round2Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SystemicPowerInfrastructurePareto20261013Exact as Prior
import DASHI.Cognition.PalantirTIAFinanceStateCapacityCrossPollination20261015Exact as PalantirTIA
import DASHI.Cognition.PalantirEarlyIntelligenceProductAcquisition20261015Exact as EarlyPalantir
import DASHI.Cognition.PalantirInstalledBaseProcurementPersistence20261015Exact as Persistence
import DASHI.Cognition.PalantirMissionExpansionContestability20261015Exact as Mission
import DASHI.Cognition.EpsteinPalantirInvestmentInterest20261015Exact as PalantirInterest
import DASHI.Cognition.EpsteinHoneycombPalantirOpportunityBridge20261015Exact as HoneycombPalantir
import DASHI.Cognition.EpsteinBarakPalantirFoundersFundBrokerage20261015Exact as Brokerage
import DASHI.Cognition.MavenMinabPineGapTargetingChainExact as Maven
import DASHI.Cognition.Project2025PalantirImmigrationDataIntersectionExact as Immigration

------------------------------------------------------------------------
-- SYSTEMIC POWER INFRASTRUCTURE PARETO — ROUND 2, 2026-10-15
--
-- The Palantir lane is promoted because several previously independent surfaces
-- are now source-paid and typed together: historical TIA disposition; early
-- In-Q-Tel financing/intelligence-community product development; generic
-- platform capabilities; modern ICE and Maven procurement; policy-capability
-- intersection; bounded installed-base persistence; concrete mission-expansion
-- test objects; direct Epstein-side Palantir investment inquiry/opportunity/
-- diligence; and Barak/Founders Fund brokerage.
-- Promotion is investigative priority, not a continuity theorem.
------------------------------------------------------------------------

data Lane2 : Set where
  palantirHistoricalCapitalCapabilityStateCapacity : Lane2
  palantirMissionExpansionContestability : Lane2
  palantirEpsteinInvestmentExecution : Lane2
  palantirBrokerageDefenseTech : Lane2
  palantirInstalledBaseContestability : Lane2
  priorSystemicFront : Lane2

record Profile2 : Set where
  constructor profile2
  field
    lane : Lane2
    priority : Nat
    directEvidenceHigh : Bool
    secondOrderLeverageHigh : Bool
    thirdOrderLeverageHigh : Bool
    sourceResolutionDebtHigh : Bool
    reading : String
open Profile2 public

canonicalSystemicFront2 : List Profile2
canonicalSystemicFront2 =
  profile2 palantirMissionExpansionContestability 100 true true true true
    "The durable-state-capacity hypothesis now has concrete mission-expansion tests: ICE/HSI FOIA records pay bulk voter-data processing, internal planning to ingest processed voter-roll data into ELITE and a later 'pending Palantir entry' state, while Palantir publicly denies completed voter-roll integration. Separately, Hilton litigation alleges observer photos/plates and related records were entered into Palantir-built ICM and propagated into enforcement/border consequences. Planning, ingestion, litigation allegation and adjudicated fact remain distinct."
  ∷ profile2 palantirHistoricalCapitalCapabilityStateCapacity 99 true true true true
    "TIA's public programme/disposition and Poindexter-Karp-Thiel context now sit beside a more concrete early Palantir acquisition spine: a bounded USD2m September-2005 In-Q-Tel investment receipt, 2005-08 intelligence-analyst co-development, an NCTC live-database prototype beta, a CIA counterterrorism-centre audition and early JIEDDO operational use. Combined with modern ICE/Maven procurement, this supports tests of capability accumulation while same-program identity, code/asset transfer and authority continuity remain unpaid."
  ∷ profile2 palantirEpsteinInvestmentExecution 99 true true true true
    "Direct Thiel advice on Palantir, a later Fiszel secondary-share opportunity routed to Epstein, and 2018 valuation/IPO diligence are paid. Execution/custody is still open. A completed position would create a direct capital edge; absent that receipt, interest/opportunity remains distinct from ownership."
  ∷ profile2 palantirInstalledBaseContestability 99 true true true true
    "Installed-base persistence is partly paid: early intelligence-user feedback and repeated adoption; historical public-record evidence of migration/data-exit difficulty; a 2026 DHS-wide single-award Palantir BPA with USD1bn ceiling/five-year horizon; and concrete ICE/CISA calls under the vehicle. Universal or unlawful lock-in, schema ownership and subject remedy remain separately unpaid."
  ∷ profile2 palantirBrokerageDefenseTech 98 true true true true
    "Epstein proposed a Palantir board route for Barak, later facilitated/attempted Thiel contact, and separately sat in the forwarding path around Carbyne's introduction to Founders Fund/Trae Stephens. These are real brokerage surfaces across distinct objects; proposal is not appointment and introduction is not investment causation."
  ∷ profile2 priorSystemicFront 100 true true true true
    "The prior systemic front remains live: banking/elite access, private-capital housing-AI-power assetisation, military AI/intelligence, Epstein/AI-capital reflexivity and other 98-100 lanes are not displaced by this Palantir-specific promotion."
  ∷ []

record Boundary2 : Set where
  constructor boundary2
  field
    genealogyEqualsProgrammeSuccession : Bool
    investmentInterestEqualsOwnership : Bool
    brokerageEqualsDecisionCausation : Bool
    genericCapabilityEqualsSpecificDeploymentUse : Bool
    repeatedProcurementEqualsLockIn : Bool
    plannedMissionExpansionEqualsDeployment : Bool
    pendingEntryEqualsCompletedIngestion : Bool
    litigationAllegationEqualsAdjudicatedFact : Bool
    sharedThielEqualsSharedCapitalOrCommand : Bool
    intelligenceCustomerAccessEqualsSovereignControl : Bool
open Boundary2 public

canonicalBoundary2 : Boundary2
canonicalBoundary2 = boundary2 false false false false false false false false false false

data GenealogyImpliesProgrammeIdentity : Set where
data InterestImpliesOwnership : Set where
data BrokerageImpliesDecisionCausation : Set where
data ProcurementImpliesLockIn : Set where
data PlannedMissionImpliesDeployment : Set where
data PendingEntryImpliesIngestion : Set where
data LitigationAllegationImpliesFact : Set where

genealogyDoesNotCreateProgrammeIdentity : GenealogyImpliesProgrammeIdentity → ⊥
genealogyDoesNotCreateProgrammeIdentity ()

interestDoesNotCreateOwnership : InterestImpliesOwnership → ⊥
interestDoesNotCreateOwnership ()

brokerageDoesNotCreateDecisionCausation : BrokerageImpliesDecisionCausation → ⊥
brokerageDoesNotCreateDecisionCausation ()

procurementDoesNotCreateLockIn : ProcurementImpliesLockIn → ⊥
procurementDoesNotCreateLockIn ()

plannedMissionDoesNotCreateDeployment : PlannedMissionImpliesDeployment → ⊥
plannedMissionDoesNotCreateDeployment ()

pendingEntryDoesNotCreateIngestion : PendingEntryImpliesIngestion → ⊥
pendingEntryDoesNotCreateIngestion ()

litigationAllegationDoesNotCreateFact : LitigationAllegationImpliesFact → ⊥
litigationAllegationDoesNotCreateFact ()

------------------------------------------------------------------------
-- Cross-domain max-cut after today's Palantir donor PR and acquisition pass.
------------------------------------------------------------------------

data Debt2 : Set where
  eliteFOIAExactPageAndIngestionOutcome : Debt2
  hiltonOperationalExhibitsAndPropagation : Debt2
  earlyIQTInstrumentAndCapTable : Debt2
  earlyIntelligenceTechnicalRecords : Debt2
  tiaSuccessorComponentAndAuthorityTransfer : Debt2
  epsteinPalantirExecutionOrExplicitDecline : Debt2
  fiszelPalantirSellerVehicle : Debt2
  palantirBPADataMigrationTerms : Debt2
  sameDeploymentSubjectContestability : Debt2
  barakPalantirAndCarbyneDecisionJoin : Debt2
  valarIIIAndurilPrimaryPortfolioRow : Debt2

record Acquisition2 : Set where
  constructor acquisition2
  field
    debt : Debt2
    priority : Nat
    instruction : String
open Acquisition2 public

canonicalAcquisition2 : List Acquisition2
canonicalAcquisition2 =
  acquisition2 eliteFOIAExactPageAndIngestionOutcome 100
    "Index the complete ICE/HSI FOIA production to exact page IDs and resolve 'pending Palantir entry' to completed voter-data ingestion, rejection, cancellation or technical deferral; preserve Palantir's contrary no-integration statement until the same object is resolved." ∷
  acquisition2 hiltonOperationalExhibitsAndPropagation 100
    "Acquire the unsealed Hilton government exhibits/ICM records and same-person event logs to resolve observer-data entry, labels, facial-recognition use, TECS/border propagation and available correction/deletion/remedy from primary carriers." ∷
  acquisition2 earlyIQTInstrumentAndCapTable 100
    "The investment amount/date and concrete product-development objects are substantially paid. Acquire the original In-Q-Tel security/investment agreement and 2005 cap table to resolve security class, economic ownership, information/board rights and contractual development/customer-access terms." ∷
  acquisition2 tiaSuccessorComponentAndAuthorityTransfer 100
    "Resolve TIA/IAO successor/transferred component names, custodians, funding, personnel authority, requirements and any code/asset transfer; do not infer Palantir succession from functional similarity." ∷
  acquisition2 epsteinPalantirExecutionOrExplicitDecline 100
    "Resolve the 2014/2016 Palantir investment-interest path to an executed trade/custody record or explicit decline/expiry." ∷
  acquisition2 fiszelPalantirSellerVehicle 100
    "Identify the holder/vehicle behind Fiszel's USD5-per-share access and determine whether Honeycomb was principal, intermediary or unrelated vehicle before claiming a fund-level Palantir investment." ∷
  acquisition2 palantirBPADataMigrationTerms 100
    "Acquire the full DHS BPA/limited-sources justification and predecessor-award chain, then resolve schema/configuration ownership, data export, transition assistance, migration rights and actual replacement attempts before promoting lock-in." ∷
  acquisition2 earlyIntelligenceTechnicalRecords 99
    "Recover the NCTC beta, CIA audition and JIEDDO technical/contract records to pay exact datasets, prototype versions, evaluation criteria, requirements and transition into paid operational use from primary government/project carriers." ∷
  acquisition2 sameDeploymentSubjectContestability 99
    "Use ELITE/Hilton as concrete test objects to pay exact subject data, classification/decision use, notice, correction/appeal, audit and remedy chains; generic Foundry capability or user-audit tooling is insufficient." ∷
  acquisition2 valarIIIAndurilPrimaryPortfolioRow 99
    "Secondary researchers point to DOJ-hosted Valar III schedules as containing an early Anduril Series Seed position. Acquire and directly inspect the exact primary schedule row before promoting Southern Trust's indirect Valar->Anduril economic exposure." ∷
  acquisition2 barakPalantirAndCarbyneDecisionJoin 98
    "Resolve Palantir's internal response to the Barak board proposal and Founders Fund's Carbyne diligence/decision separately, then measure Epstein's actual brokerage contribution rather than merging the two episodes."
  ∷ []
