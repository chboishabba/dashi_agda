module DASHI.Cognition.SystemicLeverageBeneficiaryReceiptRound20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SystemicLeverageBeneficiaryIncidenceParetoExact as Incidence

------------------------------------------------------------------------
-- SYSTEMIC LEVERAGE / BENEFICIARY RECEIPT ROUND — 2026-10-12
--
-- Only source-backed beneficiary mechanisms are paid here.  A paid benefit
-- mechanism remains distinct from motive, knowledge, coordination, wrongdoing
-- or universal explanation.
------------------------------------------------------------------------

data ReceiptLane : Set where
  bankingEliteClientAccess : ReceiptLane
  corporateNetworkConnectivity : ReceiptLane
  corporateMarketReaction : ReceiptLane
  project2025PersonnelCapacity : ReceiptLane
  project2025RegulatoryRelief : ReceiptLane
  project2025CivilServiceSelection : ReceiptLane

record BeneficiaryReceipt : Set where
  constructor beneficiary-receipt
  field
    lane : ReceiptLane
    sourceIdentity : String
    sourceRole : String
    boundedFinding : String
    beneficiaryMechanismPaid : Bool
    secondOrderEffectPaid : Bool
    thirdOrderEffectPaid : Bool
    motivePaid : Bool
    wrongdoingPaidByThisReceipt : Bool
open BeneficiaryReceipt public

bankEliteAccessReceipt : BeneficiaryReceipt
bankEliteAccessReceipt = beneficiary-receipt
  bankingEliteClientAccess
  "U.S. Senate Finance Committee Democratic staff, Looking the Other Way, 2026-08-04"
  "congressional investigative finding"
  "Committee reporting says top bank officials protected Epstein in order to gain access to Leon Black and other billionaires. This pays an attributed elite-client-access benefit mechanism; it does not prove that motive for every banker or every retention decision."
  true true false false false

corporateConnectivityReceipt : BeneficiaryReceipt
corporateConnectivityReceipt = beneficiary-receipt
  corporateNetworkConnectivity
  "Gertsberg, Pagel, Volkova, CESifo Working Paper 12580, 2026"
  "systematic working-paper network analysis"
  "Authors report that adding Epstein-mediated ties makes the S&P500 board network denser and shortens path lengths; they interpret this as Epstein wiring corporate America into a more interconnected governance network. This pays a network-topology effect under their classification method, not an individual benefit or wrongdoing claim."
  true true false false false

corporateMarketReactionReceipt : BeneficiaryReceipt
corporateMarketReactionReceipt = beneficiary-receipt
  corporateMarketReaction
  "Gertsberg, Pagel, Volkova, CESifo Working Paper 12580, 2026"
  "event-study result"
  "Authors report significantly negative cumulative abnormal returns, up to about -3.7% over a three-day window, for firms whose CEOs or directors appeared in Epstein-related news after the 2026-01-30 DOJ release. This pays a measured market-reaction channel, not causation for every firm or a welfare conclusion."
  true true false false false

projectPersonnelCapacityReceipt : BeneficiaryReceipt
projectPersonnelCapacityReceipt = beneficiary-receipt
  project2025PersonnelCapacity
  "Heritage Foundation Project 2025 primary materials + administration appointment records"
  "primary implementation architecture plus appointment receipts"
  "Project 2025 explicitly built policy, personnel, training and 180-day implementation infrastructure; key contributors including Russ Vought and Brendan Carr later entered senior administration roles. This pays a personnel-to-state-capacity bridge, not total blueprint adoption."
  true true true false false

projectRegulatoryReliefReceipt : BeneficiaryReceipt
projectRegulatoryReliefReceipt = beneficiary-receipt
  project2025RegulatoryRelief
  "Reuters 2026 reporting on Trump EPA methane and climate-regulation rollbacks"
  "current policy/reporting receipt"
  "Reuters reports administration arguments that rescinding methane controls would reduce producer compliance costs, and that repeal of the greenhouse-gas endangerment finding was promoted as reducing costs and reviving fossil-fuel and auto industries. This pays an intended/claimed regulatory-relief channel; quantified savings and downstream welfare remain contested."
  true true false false false

projectCivilServiceSelectionReceipt : BeneficiaryReceipt
projectCivilServiceSelectionReceipt = beneficiary-receipt
  project2025CivilServiceSelection
  "Reuters investigation, 2025-08-07, American Accountability Foundation federal-worker watchlists"
  "investigative reporting"
  "Reuters reports a Heritage-funded pro-Trump group targeted 175 federal employees on public watchlists as part of an effort to identify and remove workers viewed as hostile to the administration agenda; reported consequences included harassment, fear and departures. This pays a personnel-selection/chilling-effect pathway, not Heritage control of every removal."
  true true true false false

canonicalReceipts : List BeneficiaryReceipt
canonicalReceipts =
  bankEliteAccessReceipt
  ∷ corporateConnectivityReceipt
  ∷ corporateMarketReactionReceipt
  ∷ projectPersonnelCapacityReceipt
  ∷ projectRegulatoryReliefReceipt
  ∷ projectCivilServiceSelectionReceipt
  ∷ []

------------------------------------------------------------------------
-- Multiobjective current frontier.
------------------------------------------------------------------------

data SystemicFrontierLane : Set where
  bankMoneyComplianceEliteAccess : SystemicFrontierLane
  corporateBoardTopology : SystemicFrontierLane
  project2025PolicyPersonnelStateCapacity : SystemicFrontierLane
  trumpMarALagoBannonAccessNarrative : SystemicFrontierLane
  edgeMITScienceTechBrokerage : SystemicFrontierLane
  thielPalantirInvestmentProcurement : SystemicFrontierLane
  rinehartOneNationPoliticalCapacity : SystemicFrontierLane

record FrontierProfile : Set where
  constructor frontier-profile
  field
    frontierLane : SystemicFrontierLane
    directEvidenceGainHigh : Bool
    crossLaneBridgeHigh : Bool
    secondOrderLeverageHigh : Bool
    thirdOrderLeverageHigh : Bool
    incidenceDebtHigh : Bool
    sourceAvailabilityHigh : Bool
    redundancyLow : Bool
    routingReading : String
open FrontierProfile public

bankProfile : FrontierProfile
bankProfile = frontier-profile
  bankMoneyComplianceEliteAccess
  true true true true true true true
  "Undominated: direct transaction evidence, executive/compliance decision chain, explicit elite-client-access benefit allegation, unreleased FBI 302s and high beneficiary/burden incidence debt."

boardProfile : FrontierProfile
boardProfile = frontier-profile
  corporateBoardTopology
  true true true true true true true
  "Undominated: systematic universe, network-topology effects and market reaction, but high person-level resolution debt."

project2025Profile : FrontierProfile
project2025Profile = frontier-profile
  project2025PolicyPersonnelStateCapacity
  true true true true true true true
  "Undominated: policy-to-personnel-to-state conversion plus second-order regulatory incidence and third-order capacity/selection effects."

trumpProfile : FrontierProfile
trumpProfile = frontier-profile
  trumpMarALagoBannonAccessNarrative
  true true true true true true true
  "Undominated: paid historical/social/access edges plus unresolved knowledge, recruitment-locus, media/narrative and records-governance effects."

edgeProfile : FrontierProfile
edgeProfile = frontier-profile
  edgeMITScienceTechBrokerage
  true true true false true true true
  "High but currently below the four-systemic-front set because third-order institutional effects remain less directly resolved than banking/boards/state-capacity/Trump-world lanes."

thielProfile : FrontierProfile
thielProfile = frontier-profile
  thielPalantirInvestmentProcurement
  true true true true true true true
  "Potentially undominated once direct investment/introduction/procurement bridges are document-resolved; current coordination debt remains high."

rinehartProfile : FrontierProfile
rinehartProfile = frontier-profile
  rinehartOneNationPoliticalCapacity
  true true true true true true true
  "Potentially undominated regionally: money/logistics/access/policy-input/recruitment capacity plus Queensland resource-policy intersection, with direct Epstein edge still unpaid."

currentUndominatedSystemicFrontier : List FrontierProfile
currentUndominatedSystemicFrontier =
  bankProfile
  ∷ boardProfile
  ∷ project2025Profile
  ∷ trumpProfile
  ∷ []

currentNearFrontier : List FrontierProfile
currentNearFrontier =
  thielProfile
  ∷ rinehartProfile
  ∷ edgeProfile
  ∷ []

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PaidBenefitMechanismImpliesMotive : Set where
data RegulatoryReliefImpliesNetSocialBenefit : Set where
data NegativeMarketReactionImpliesWrongdoing : Set where
data NetworkDensityImpliesCoordination : Set where
data PersonnelSelectionImpliesIllegalPurge : Set where

data ThirdOrderEffectImpliesIntent : Set where

paidBenefitDoesNotCreateMotive : PaidBenefitMechanismImpliesMotive → ⊥
paidBenefitDoesNotCreateMotive ()

regulatoryReliefDoesNotCreateNetSocialBenefit : RegulatoryReliefImpliesNetSocialBenefit → ⊥
regulatoryReliefDoesNotCreateNetSocialBenefit ()

marketReactionDoesNotCreateWrongdoing : NegativeMarketReactionImpliesWrongdoing → ⊥
marketReactionDoesNotCreateWrongdoing ()

networkDensityDoesNotCreateCoordination : NetworkDensityImpliesCoordination → ⊥
networkDensityDoesNotCreateCoordination ()

personnelSelectionDoesNotCreateIllegality : PersonnelSelectionImpliesIllegalPurge → ⊥
personnelSelectionDoesNotCreateIllegality ()

thirdOrderDoesNotCreateIntent : ThirdOrderEffectImpliesIntent → ⊥
thirdOrderDoesNotCreateIntent ()
