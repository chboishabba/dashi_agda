module DASHI.Governance.PetroleumFinancialRoutingNoncollapseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.TrumpEnergyCrackSpreadCrossPollinationExact as Energy
import DASHI.Governance.IranContraCovertFlowHistoricalMechanismExact as IranContra

------------------------------------------------------------------------
-- PETROLEUM / FINANCIAL ROUTING NONCOLLAPSE
--
-- Historical oil-dollar settlement structures, Iran/Contra covert flows and
-- current Iran sanctions-evasion allegations are distinct mechanism classes.
------------------------------------------------------------------------

frusSaudi1973 : Source.AttributedSource
frusSaudi1973 = Source.mkNoDOISource
  "U.S. Department of State, Office of the Historian"
  "FRUS 1969-1976, Vol. XXXVI, doc. 200: Saudi petrodollars"
  "Foreign Relations of the United States"
  "1973-09-04"
  "https://history.state.gov/historicaldocuments/frus1969-76v36/d200"
  Source.governmentSource
  "primary diplomatic record using the term petrodollars and discussing Saudi oil revenue, currency allocation and investment concerns; not proof of a single secret petrodollar pact"
  Source.publicAttribution

frusIranOil1975 : Source.AttributedSource
frusIranOil1975 = Source.mkNoDOISource
  "U.S. Department of State, Office of the Historian"
  "FRUS 1969-1976, Vol. XXVII, doc. 122: Iran Bilateral Oil Deal"
  "Foreign Relations of the United States"
  "1975-05-13"
  "https://history.state.gov/historicaldocuments/frus1969-76v27/d122"
  Source.governmentSource
  "primary U.S. memorandum discussing a proposed Iran-U.S. oil arrangement involving Treasury notes and purchases of U.S. goods; proposal status retained"
  Source.publicAttribution

treasuryShadowFleet2026 : Source.AttributedSource
treasuryShadowFleet2026 = Source.mkNoDOISource
  "U.S. Department of the Treasury"
  "Treasury Targets Iran's Shadow Fleet, Networks Supplying Ballistic Missile and ACW Programs"
  "Treasury press release"
  "2026-02-25"
  "https://home.treasury.gov/news/press-releases/sb0405"
  Source.governmentSource
  "U.S. sanctions authority alleges shadow-fleet petroleum revenues finance repression, proxies and weapons; allegation/administrative designation is not independent adjudication of every downstream-use claim"
  Source.publicAttribution

reutersChinaBarter2026 : Source.AttributedSource
reutersChinaBarter2026 = Source.mkNoDOISource
  "Reuters"
  "How a billion-dollar sanctions dodge kept Chinese goods flowing to Iran"
  "Reuters"
  "2026-09-10"
  "https://www.reuters.com/world/asia-pacific/how-billion-dollar-sanctions-dodge-kept-chinese-goods-flowing-iran-2026-09-10/"
  Source.newsSource
  "investigative reporting on an alleged barter-like oil-for-goods/SPV route bypassing conventional banking; source claims and denials remain separately attributed"
  Source.publicAttribution

data PetroleumRoutingClass : Set where
  ordinaryOilSettlement : PetroleumRoutingClass
  sovereignReserveInvestment : PetroleumRoutingClass
  proposedBilateralOilCredit : PetroleumRoutingClass
  sanctionsEvasionRouting : PetroleumRoutingClass
  covertArmsFundsDiversion : PetroleumRoutingClass

record RoutingMechanismReceipt : Set where
  constructor routing-mechanism-receipt
  field
    class : PetroleumRoutingClass
    sourceRef : String
    carrier : String
    intermediary : String
    settlementOrFlow : String
    downstreamUse : String
    sourceRole : String
    covertIntentPaid : Bool
    sanctionsEvasionPaid : Bool
    illegalDiversionPaid : Bool

open RoutingMechanismReceipt public

saudiPetrodollarReceipt : RoutingMechanismReceipt
saudiPetrodollarReceipt =
  routing-mechanism-receipt
    sovereignReserveInvestment
    "FRUS 1973 Saudi petrodollars"
    "oil revenue"
    "Saudi state / financial institutions"
    "multi-currency positioning and reserve/investment questions"
    "state reserves and investment"
    "primary diplomatic observation"
    false false false

iranBilateralOilProposalReceipt : RoutingMechanismReceipt
iranBilateralOilProposalReceipt =
  routing-mechanism-receipt
    proposedBilateralOilCredit
    "FRUS 1975 Iran Bilateral Oil Deal"
    "Iranian oil"
    "private importers + U.S. Treasury proposal"
    "cash receipt / Treasury notes / later U.S.-goods purchases"
    "bilateral trade proposal"
    "primary proposal memorandum; not completed-deal proof"
    false false false

currentIranBarterReceipt : RoutingMechanismReceipt
currentIranBarterReceipt =
  routing-mechanism-receipt
    sanctionsEvasionRouting
    "Reuters 2026-09-10 + U.S. Treasury sanctions surface"
    "Iranian oil revenue"
    "China-linked SPV / trading entities as reported"
    "oil-for-goods / nonstandard financial routing"
    "Chinese goods / Iranian projects and procurement as reported"
    "investigative reporting plus sanctions-authority allegations"
    false true false

iranContraReceipt : RoutingMechanismReceipt
iranContraReceipt =
  routing-mechanism-receipt
    covertArmsFundsDiversion
    "IranContraCovertFlowHistoricalMechanismExact"
    "arms-sale proceeds"
    "North/Secord/Hakim Enterprise"
    "off-the-books corporate / Swiss-account flow"
    "Contra support"
    "historical Independent Counsel / archival record"
    true false true

record RoutingNoncollapseBoundary : Set where
  constructor routing-noncollapse-boundary
  field
    oilDollarSettlementEqualsSecretPact : Bool
    ordinarySettlementEqualsSanctionsEvasion : Bool
    sanctionsEvasionEqualsIranContra : Bool
    sameIntermediaryTopologyEqualsSameLegality : Bool
    sameDownstreamMilitaryUseEqualsSameMechanism : Bool
    currentOilRoutingProvesHistoricalContinuity : Bool

open RoutingNoncollapseBoundary public

canonicalBoundary : RoutingNoncollapseBoundary
canonicalBoundary =
  routing-noncollapse-boundary false false false false false false

data PetrodollarMeansSingleSecretAgreement : Set where
data SanctionsEvasionMeansIranContraMechanism : Set where
data ResourceRevenueMeansMilitaryFundingByDefinition : Set where
data CurrentIranRoutingProvesHistoricalContinuity : Set where

petrodollarDoesNotMeanSingleSecretAgreement :
  PetrodollarMeansSingleSecretAgreement → ⊥
petrodollarDoesNotMeanSingleSecretAgreement ()

sanctionsEvasionDoesNotEqualIranContra :
  SanctionsEvasionMeansIranContraMechanism → ⊥
sanctionsEvasionDoesNotEqualIranContra ()

resourceRevenueDoesNotDefineDownstreamUse :
  ResourceRevenueMeansMilitaryFundingByDefinition → ⊥
resourceRevenueDoesNotDefineDownstreamUse ()

currentRoutingDoesNotProveHistoricalContinuity :
  CurrentIranRoutingProvesHistoricalContinuity → ⊥
currentRoutingDoesNotProveHistoricalContinuity ()

historicalIranContra :
  IranContra.HistoricalRoutingTopology
historicalIranContra = IranContra.iranContraTopology

currentEnergySnapshot :
  Energy.EnergyMarketSnapshot
currentEnergySnapshot = Energy.eia20260827Close

treasurySnowball :
  Snowball.SourceRoleSnowballReceipt treasuryShadowFleet2026
treasurySnowball =
  Snowball.canonicalSourceRoleSnowballReceipt treasuryShadowFleet2026
