module DASHI.Cognition.SystemicLeverageBeneficiaryReceiptRound20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SystemicLeverageBeneficiaryIncidenceParetoExact as Incidence
import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as Cambridge
import DASHI.Cognition.Project2025PalantirImmigrationDataIntersectionExact as PalantirIntersection

------------------------------------------------------------------------
-- SYSTEMIC LEVERAGE / BENEFICIARY RECEIPT ROUND — 2026-10-12/13
--
-- Only source-backed beneficiary/capability mechanisms are paid here. A paid
-- benefit or capability mechanism remains distinct from motive, knowledge,
-- coordination, wrongdoing, persuasion, policy authorship or universal cause.
------------------------------------------------------------------------

data ReceiptLane : Set where
  bankingEliteClientAccess : ReceiptLane
  corporateNetworkConnectivity : ReceiptLane
  corporateMarketReaction : ReceiptLane
  bannonTargetedInfluenceInfrastructure : ReceiptLane
  project2025PersonnelCapacity : ReceiptLane
  project2025RegulatoryRelief : ReceiptLane
  project2025CivilServiceSelection : ReceiptLane
  project2025PalantirPolicyCapabilityIntersection : ReceiptLane

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
  "Authors report a changed corporate-board network topology when Epstein-mediated ties are added. Revised mechanism tests do not make own centrality gain the misconduct mechanism. Topology/exposure is paid; individual benefit is not inferred."
  true true false false false

corporateMarketReactionReceipt : BeneficiaryReceipt
corporateMarketReactionReceipt = beneficiary-receipt
  corporateMarketReaction
  "Gertsberg, Pagel, Volkova, CESifo Working Paper 12580, revised 2026"
  "event-study result"
  "Authors report significantly negative cumulative abnormal returns, up to about -3.7% over a three-day window, for firms whose CEOs or directors appeared in Epstein-related news after the 2026-01-30 DOJ release. This pays a measured market-reaction channel, not causation for every firm or a wrongdoing/welfare conclusion."
  true true false false false

bannonInfluenceReceipt : BeneficiaryReceipt
bannonInfluenceReceipt = beneficiary-receipt
  bannonTargetedInfluenceInfrastructure
  "UK Parliament DCMS reports + US FTC Cambridge Analytica order + FEC records"
  "parliamentary/regulatory/campaign-finance receipts"
  "Bannon/Cambridge Analytica/SCL/Mercer infrastructure, deceptive Facebook-data harvesting for voter profiling, substantial Trump-campaign vendor payments and cross-Atlantic political brokerage are source-paid. This pays targeting/narrative capability and brokerage; it does not pay universal psychographic efficacy, election causation, illegal common-vendor coordination, or later reuse in Bannon's Epstein media work."
  true true true false false

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
  "Project 2025 chapter texts + 2026 administration/FCC/EPA implementation records and reporting"
  "policy-to-action incidence receipts"
  "Concrete author/office/action correspondences now include Vought/OMB and Carr/FCC. Some actions expand removal/control or deregulatory/consolidation option value. The recipient/beneficiary incidence is separately auditable; net welfare and Project-2025 causation are not inferred."
  true true true false false

projectCivilServiceSelectionReceipt : BeneficiaryReceipt
projectCivilServiceSelectionReceipt = beneficiary-receipt
  project2025CivilServiceSelection
  "Reuters investigation 2025-08-07 + 2026 civil-service implementation reporting"
  "investigative/current implementation reporting"
  "A Heritage-funded pro-Trump group targeted 175 federal employees on public watchlists, while later civil-service reforms increased political removal/control capacity over a much larger policy-influencing workforce. This pays a personnel-selection/state-capacity pathway, not Heritage control of every removal or illegality."
  true true true false false

projectPalantirReceipt : BeneficiaryReceipt
projectPalantirReceipt = beneficiary-receipt
  project2025PalantirPolicyCapabilityIntersection
  "Project 2025 DHS chapter + ICE procurement justifications + USAspending 70CTD026FC0000012"
  "primary policy/procurement intersection"
  "Project 2025 independently demands stronger immigration-agency/data integration; ICE independently deploys Palantir ICM/ImmigrationOS targeting and case-management capability and awarded an approximately USD 86.27m ERO-related order in April 2026. This pays a policy-demand/capability/procurement intersection and downstream lock-in/exit questions; it does not pay Project 2025 vendor selection or abuse."
  true true true false false

canonicalReceipts : List BeneficiaryReceipt
canonicalReceipts =
  bankEliteAccessReceipt
  ∷ corporateConnectivityReceipt
  ∷ corporateMarketReactionReceipt
  ∷ bannonInfluenceReceipt
  ∷ projectPersonnelCapacityReceipt
  ∷ projectRegulatoryReliefReceipt
  ∷ projectCivilServiceSelectionReceipt
  ∷ projectPalantirReceipt
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
  "Undominated: direct transaction evidence, executive/compliance decision chain, explicit elite-client-access benefit allegation, BNY transaction/cash probe, unreleased banker FBI 302s and high beneficiary/burden incidence debt."

boardProfile : FrontierProfile
boardProfile = frontier-profile
  corporateBoardTopology
  true true true true true true true
  "Undominated: revised systematic public-firm universe, network/exposure mechanism and market reaction, but high person-level primary-document and benefit-incidence resolution debt."

project2025Profile : FrontierProfile
project2025Profile = frontier-profile
  project2025PolicyPersonnelStateCapacity
  true true true true true true true
  "Undominated: chapter->author->office->action chains, policy-to-personnel state conversion, civil-service/media-ownership incidence, and a paid immigration data-demand x Palantir/ICE capability intersection with vendor-selection causation explicitly unpaid."

trumpProfile : FrontierProfile
trumpProfile = frontier-profile
  trumpMarALagoBannonAccessNarrative
  true true true true true true true
  "Undominated: paid historical/social/access and Mar-a-Lago recruitment-locus edges plus Bannon's source-paid Cambridge-Analytica/SCL/Mercer targeting/brokerage infrastructure and later Epstein media relationship. The high-value residual is same-technique transfer, knowledge and downstream narrative/disclosure effects—not presumed election causation."

edgeProfile : FrontierProfile
edgeProfile = frontier-profile
  edgeMITScienceTechBrokerage
  true true true false true true true
  "High but currently below the four-systemic-front set because third-order institutional effects remain less directly resolved than banking/boards/state-capacity/Trump-world lanes."

thielProfile : FrontierProfile
thielProfile = frontier-profile
  thielPalantirInvestmentProcurement
  true true true true true true true
  "Near-frontier: current Palantir state procurement/data capability is now strongly paid, but the distinct Epstein->Thiel/Valar/Barak and Project2025->vendor-selection bridges still require document-local resolution."

rinehartProfile : FrontierProfile
rinehartProfile = frontier-profile
  rinehartOneNationPoliticalCapacity
  true true true true true true true
  "Potentially undominated regionally: money/logistics/access/policy-input/recruitment capacity plus Queensland resource-policy intersection, with direct Epstein and Rinehart->Crisafulli brokerage edges still unpaid."

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

cambridgeSourceBoundary : Cambridge.BannonInfluenceInfrastructureBoundary
cambridgeSourceBoundary = Cambridge.canonicalBannonInfluenceInfrastructureBoundary

palantirIntersectionBoundary : PalantirIntersection.Project2025PalantirBoundary
palantirIntersectionBoundary = PalantirIntersection.canonicalProject2025PalantirBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PaidBenefitMechanismImpliesMotive : Set where
data RegulatoryReliefImpliesNetSocialBenefit : Set where
data NegativeMarketReactionImpliesWrongdoing : Set where
data NetworkDensityImpliesCoordination : Set where
data PersonnelSelectionImpliesIllegalPurge : Set where
data TargetingCapabilityImpliesElectionCause : Set where
data PolicyCapabilityIntersectionImpliesVendorSelection : Set where
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

targetingCapabilityDoesNotCreateElectionCause : TargetingCapabilityImpliesElectionCause → ⊥
targetingCapabilityDoesNotCreateElectionCause ()

policyCapabilityIntersectionDoesNotCreateVendorSelection : PolicyCapabilityIntersectionImpliesVendorSelection → ⊥
policyCapabilityIntersectionDoesNotCreateVendorSelection ()

thirdOrderDoesNotCreateIntent : ThirdOrderEffectImpliesIntent → ⊥
thirdOrderDoesNotCreateIntent ()
