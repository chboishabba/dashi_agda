module DASHI.Cognition.SpringfieldValueCaptureReceiptRound20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SpringfieldLayeredValueCaptureParetoExact as Pareto
import DASHI.Cognition.BlackRockMirvacSpringfieldCapitalOverlapExact as Capital
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as GasLobby
import DASHI.Law.SensibLawSpringfieldEnergyTransitionLineageExact as Energy
import DASHI.Law.SensibLawWoogarooExternalEvidenceSourceAuditExact as Ecology

------------------------------------------------------------------------
-- GREATER SPRINGFIELD VALUE-CAPTURE RECEIPT ROUND — 2026-10-14
--
-- This module pays only source-local propositions.  It distinguishes:
--   * legal/acquisition vehicle from ultimate beneficial ownership;
--   * network-level gas ownership from exact Springfield service-line title;
--   * lobbying subject labels from policy causation or gas-specific asks;
--   * listed-equity exposure from operational control;
--   * master-developer land allocation from downstream parcel ownership;
--   * public infrastructure support from a subsidy-to-private-benefit theorem.
------------------------------------------------------------------------

data ReceiptClass : Set where
  governmentRegistry : ReceiptClass
  governmentDiary : ReceiptClass
  governmentInfrastructure : ReceiptClass
  companyPrimary : ReceiptClass
  regulatorPrimary : ReceiptClass
  firstPartyTransaction : ReceiptClass
  contemporaneousNewsLocator : ReceiptClass
  currentNewsTransaction : ReceiptClass

record Receipt : Set where
  constructor receipt
  field
    label : String
    sourceClass : ReceiptClass
    source : String
    boundedFinding : String
    paid : Bool
open Receipt public

------------------------------------------------------------------------
-- City West: exact acquisition structure is partly paid.
------------------------------------------------------------------------

cityWestABRVehicle : Receipt
cityWestABRVehicle = receipt
  "City West acquisition partnership ABN"
  governmentRegistry
  "Australian Business Register — ABN 30 413 782 449"
  "The active entity is THE TRUSTEE FOR GORDON SPRINGFIELD WEST UNIT TRUST & THE TRUSTEE FOR SPRINGFIELD BJM LANDLORD TRUST, an Other Partnership active from 1 July 2024 and GST-registered from 18 August 2025. This pays an exact acquisition/project vehicle coordinate; it does not identify every trustee company, unit-holder, lender, guarantee, beneficial split or secured party."
  true

cityWestTransaction : Receipt
cityWestTransaction = receipt
  "City West AUD 50m transaction"
  currentNewsTransaction
  "2026 Springfield City West transaction reporting / Gordon Corp first-party announcement"
  "Gordon Corp and the Mathieson family acquired the 12.7 ha City West town-centre site from Springfield City Group for AUD 50 million. Reporting identifies mixed retail, commercial, entertainment, leisure and residential uses; the first Springfield Village retail/lifestyle stage is planned around a Coles anchor and other committed tenants."
  true

cityWestCapitalStackResidual : Receipt
cityWestCapitalStackResidual = receipt
  "City West debt/equity capital stack"
  governmentRegistry
  "Current public-search round"
  "The acquisition partnership and transaction counterparties are identifiable, but no public same-object lender, mortgage/security package, equity percentage, guarantee schedule or development-funding facility was located in this round."
  false

------------------------------------------------------------------------
-- Gas network lineage: network-level chain paid; exact local asset weld open.
------------------------------------------------------------------------

springfieldEnergexAlliance2004 : Receipt
springfieldEnergexAlliance2004 = receipt
  "Springfield Energex gas/electric alliance"
  contemporaneousNewsLocator
  "ABC News, 30 April 2004"
  "ABC contemporaneously reported an alliance between Energex and Springfield Land Corporation to develop gas and electricity networks at Springfield; Energex referred to approximately 8,000 gas connections. The original alliance instrument remains unlocated."
  true

allgasSale2006 : Receipt
allgasSale2006 = receipt
  "Energex to APT/APA Allgas sale"
  regulatorPrimary
  "AER/AEMC historical Allgas material"
  "Regulatory material records Australian Pipeline Trust/APA purchasing the Allgas network from Energex in 2006. This closes the network-level Energex-to-Allgas/APA transition, but not an exact cadastral/service-line proof that each Springfield segment created under the 2004 alliance transferred in that transaction."
  true

allgasOwnership2026 : Receipt
allgasOwnership2026 = receipt
  "Allgas current ownership/operator"
  regulatorPrimary
  "AEMC gas-pipeline register / Stonepeak acquisition announcement"
  "In March 2026 the Allgas distribution system transferred from GDI, owned by Marubeni (40%), SAS Trustee Corporation (40%) and APA (20%), to Stonepeak; AGIG became operator. The network is about 3,900 km and serves about 120,000 customers."
  true

springfieldExactGasAssetWeld : Receipt
springfieldExactGasAssetWeld = receipt
  "Exact Springfield gas asset weld"
  regulatorPrimary
  "Network-level ownership sources plus Springfield 2004 alliance locator"
  "The chronology now supports Energex Springfield buildout -> 2006 Energex Allgas sale -> later GDI/APA lineage -> 2026 Stonepeak/AGIG at network level. Exact Springfield easements, asset IDs, service-line maps or sale schedules tying the 2004 Springfield works into the transferred Allgas asset register remain unpaid."
  false

------------------------------------------------------------------------
-- ENGIE transition / infrastructure overlay.
------------------------------------------------------------------------

engieFiftyYearAlliance : Receipt
engieFiftyYearAlliance = receipt
  "Springfield-ENGIE 50-year strategic alliance"
  companyPrimary
  "ENGIE press release and corporate prospectus, 6 December 2018"
  "ENGIE and Springfield City Group announced a 50-year strategic alliance aimed at a net-zero-energy Greater Springfield, covering renewable generation and storage, district energy, green mobility, digital technology, energy efficiency and research/innovation. ENGIE innovation material described the arrangement as a 50-year exclusive strategic alliance."
  true

------------------------------------------------------------------------
-- Lobbying/access: repeated subject labels are now paid.
------------------------------------------------------------------------

santoroHealthUpdateJan2025 : Receipt
santoroHealthUpdateJan2025 = receipt
  "Springfield/Santoro Health portfolio meeting"
  governmentDiary
  "Queensland Health Minister diary, 16 January 2025"
  "The diary records Maha Sinnathamby, Raynuha Sinnathamby, Bob Sharpless and registered lobbyist Santo Santoro in a meeting to introduce Springfield City Group and provide an update on Springfield."
  true

santoroIntroFeb2025 : Receipt
santoroIntroFeb2025 = receipt
  "Springfield/Santoro introductory lobbying meeting"
  governmentDiary
  "Queensland Minister for Customer Services/Open Data/Small and Family Business diary, 4 February 2025"
  "The diary records Santo Santoro as lobbyist with Maha Sinnathamby, Raynuha Sinnathamby, Russell Luhrs and Jim Varghese at a Lobbyist Introductory Meeting."
  true

santoroFinanceFeb2025 : Receipt
santoroFinanceFeb2025 = receipt
  "Springfield/Santoro Finance-Trade meeting"
  governmentDiary
  "Queensland Minister for Finance, Trade, Employment and Training diary, 12 February 2025"
  "The diary records Richard Eden, Maha Sinnathamby, Bob Sharpless and Santo Santoro (registered lobbyist) at a Springfield Land Corporation Meeting. The diary does not specify a gas, planning or financial ask."
  true

santoroFinancePlanJul2025 : Receipt
santoroFinancePlanJul2025 = receipt
  "Santoro update on Springfield City Group Plan"
  governmentDiary
  "Queensland Minister for Finance, Trade, Employment and Training diary, 10 July 2025"
  "The diary records Minister Ros Bates and registered lobbyist Santo Santoro at a meeting described as an update on the Springfield City Group Plan. This pays plan-level subject matter but not the contents, requested decision, beneficiary or policy outcome."
  true

santoroGasSpecificAskResidual : Receipt
santoroGasSpecificAskResidual = receipt
  "Gas/energy-specific lobbying ask"
  governmentDiary
  "2025 ministerial-diary round"
  "Repeated Springfield/Santoro access and Springfield-plan subject matter are paid. No located diary or public lobbying record in this round identifies a gas-network, ENGIE, Allgas, energy-regulation or specific development approval ask."
  false

------------------------------------------------------------------------
-- Mirvac / Orion transaction and BlackRock equity exposure.
------------------------------------------------------------------------

mirvacOrionAgreement2002 : Receipt
mirvacOrionAgreement2002 = receipt
  "Mirvac Orion acquisition/agreement chronology"
  companyPrimary
  "Mirvac Orion Springfield Central portfolio page / FY26 property compendium"
  "Mirvac reports an acquisition/agreement date of August 2002 for Orion Springfield Central, 100% ownership, and a 30 June 2026 valuation of AUD 518 million including sundry vacant land. Mirvac states it developed Orion, which opened in 2007 and expanded in 2016."
  true

mirvacSpringfieldCounterpartyResidual : Receipt
mirvacSpringfieldCounterpartyResidual = receipt
  "Original Mirvac-Springfield counterparty instrument"
  companyPrimary
  "Current Mirvac public portfolio/history sources"
  "Current Mirvac sources pay the 2002 agreement date, development chronology, ownership, income asset and vacant-land coordinates. The original 2002 sale/development instrument, Springfield-side counterparty, price, covenants, retained rights and any revenue-sharing terms remain unpaid."
  false

blackRockMirvac2025 : Receipt
blackRockMirvac2025 = receipt
  "BlackRock Mirvac substantial holding 2025"
  companyPrimary
  "Mirvac FY25 annual report"
  "Mirvac's FY25 annual report records BlackRock Group at 263,029,096 stapled securities, 6.66% of issued equity, as at its 28 February 2025 substantial-holding notice."
  true

blackRockMirvac2026 : Receipt
blackRockMirvac2026 = receipt
  "BlackRock Mirvac substantial holding 2026"
  companyPrimary
  "Mirvac FY26 substantial-securityholder disclosure"
  "Mirvac's 2026 securityholder disclosure records BlackRock Group at 303,997,515 stapled securities, 7.70% of issued equity, with the relevant change dated 2 April 2026. This pays increased disclosed equity/voting exposure, not active management of Orion or Springfield."
  true

blackRockUnderlyingFundResidual : Receipt
blackRockUnderlyingFundResidual = receipt
  "BlackRock Mirvac underlying-fund allocation"
  companyPrimary
  "Substantial-holder and public fund disclosures"
  "The aggregate BlackRock Group substantial holding is paid. The exact decomposition across index funds, active funds, mandates, securities-lending positions, derivatives and voting instructions is not fully resolved by the annual-report summary alone."
  false

------------------------------------------------------------------------
-- Master-developer residual land / option-value surface.
------------------------------------------------------------------------

springfieldCityWestSale : Receipt
springfieldCityWestSale = receipt
  "Springfield City Group City West divestment"
  currentNewsTransaction
  "2026 City West sale reporting"
  "Springfield City Group sold the 12.7 ha City West site after decades of stewardship; the sale attracted multiple formal offers and transferred a major town-centre development option to Gordon Corp/Mathieson interests."
  true

springfieldVantageMarket : Receipt
springfieldVantageMarket = receipt
  "Springfield City Group Vantage residential land"
  firstPartyTransaction
  "Ray White/JLL marketing on behalf of Springfield City Group"
  "Springfield City Group is separately marketing the 5.83 ha Vantage Springfield Central landholding for medium-density residential/retirement/aged-care/child-care uses, with a concept plan for 217 townhouses subject to approval. This pays continuing retained-land sale/option activity beyond City West."
  true

springfieldPartnerSearch2020 : Receipt
springfieldPartnerSearch2020 = receipt
  "Springfield long-horizon development partner search"
  currentNewsTransaction
  "2020 reporting on Springfield City Group / Moelis Australia partner search"
  "Springfield City Group sought a partner or consortium to accelerate completion of the wider masterplan; reporting stated only about 25% was complete at that time and identified prior long-term partnerships including Lendlease, Aveo/Brookfield and R&F Properties. This is historical context, not a current ownership map."
  true

springfieldResidualParcelMap : Receipt
springfieldResidualParcelMap = receipt
  "Current retained/sold/optioned parcel map"
  companyPrimary
  "Current Springfield City Group transaction/marketing/public-plan sources"
  "City West sale plus Vantage marketing prove continuing parcel allocation and monetisation. A complete current cadastral map of Springfield City Group retained parcels, options, JVs, reversionary rights and continuing revenue interests remains unpaid."
  false

------------------------------------------------------------------------
-- Public/private infrastructure incidence.
------------------------------------------------------------------------

springfieldRailPublicCapital : Receipt
springfieldRailPublicCapital = receipt
  "Springfield rail public capital"
  governmentInfrastructure
  "Queensland Government Springfield Rail Project announcements"
  "The Queensland Government funded the Darra-Richlands-Springfield rail buildout, including a AUD 475 million Richlands-to-Springfield section after an earlier AUD 800 million Darra-to-Richlands stage. This pays major public transport capital supporting the growth corridor; it does not quantify private land-value uplift attributable to rail."
  true

springfieldRoadPublicCapital : Receipt
springfieldRoadPublicCapital = receipt
  "Springfield road public capital"
  governmentInfrastructure
  "Australian/Queensland/Ipswich transport-program sources"
  "Public funding has supported Springfield road-capacity works, including a federal AUD 3.46753 million contribution to a AUD 13.715187 million Springfield Parkway duplication project and Queensland TMR contributions to Springfield Greenbank Arterial/Centenary interchange works."
  true

ipswichInfrastructureChargeBoundary : Receipt
ipswichInfrastructureChargeBoundary = receipt
  "Ipswich infrastructure-charge incidence"
  governmentInfrastructure
  "Ipswich City Council infrastructure-planning guidance"
  "Council states trunk infrastructure is funded in part by developer infrastructure charges, that state-capped charges are insufficient for all required growth infrastructure, and that Council supplements costs from other sources. Charges attach to land and can include offsets/refunds or infrastructure agreements. This pays a mixed public/private financing mechanism, not a project-specific subsidy amount."
  true

projectSpecificSubsidyResidual : Receipt
projectSpecificSubsidyResidual = receipt
  "Project-specific public/private incidence"
  governmentInfrastructure
  "Infrastructure-charge registers, ICNs, state/federal project funding and development agreements"
  "The system-level rule that public capital and capped developer charges jointly fund growth infrastructure is paid. Exact parcel-by-parcel charges, offsets, refunds, public works, private contributions and resulting land-value uplift for Orion, City West, Vantage and Woogaroo parcels remain to be joined."
  false

------------------------------------------------------------------------
-- Ecological parcel join reuses the existing Woogaroo source-audit machinery.
------------------------------------------------------------------------

ecologicalParcelCarrierPaid : Receipt
ecologicalParcelCarrierPaid = receipt
  "Woogaroo/Springview parcel-impact carrier set"
  governmentInfrastructure
  "Existing SensibLawWoogarooExternalEvidenceSourceAuditExact"
  "The repo already identifies exact Council/EPBC carrier IDs for vegetation-clearing, civil-works and landscaping approvals and records the need for exact project-footprint/corridor joins. This pays acquisition routing and project identity, not every parcel-level ecological magnitude."
  true

ecologicalValueJoinResidual : Receipt
ecologicalValueJoinResidual = receipt
  "Parcel-level private value versus ecological burden join"
  governmentInfrastructure
  "Woogaroo Council/EPBC carriers plus title/transaction/value records"
  "The environmental carrier set and development/value-capture machinery both exist, but a single same-parcel table joining sale/development value, infrastructure benefit, habitat clearing, offsets, heat/water/traffic and cumulative connectivity loss remains open."
  false

------------------------------------------------------------------------
-- Explicit blockers.
------------------------------------------------------------------------

data ABNVehicleImpliesBeneficialSplit : Set where
data NetworkSaleImpliesExactSpringfieldAsset : Set where
data LobbyingMeetingImpliesGasAsk : Set where
data SpringfieldPlanMeetingImpliesDecisionOutcome : Set where
data SubstantialHoldingImpliesOperationalControl : Set where
data PublicInfrastructureImpliesPrivateSubsidyAmount : Set where
data ParcelSaleImpliesMasterControlTransferred : Set where

abnVehicleDoesNotCreateBeneficialSplit : ABNVehicleImpliesBeneficialSplit → ⊥
abnVehicleDoesNotCreateBeneficialSplit ()

networkSaleDoesNotCreateExactSpringfieldAsset : NetworkSaleImpliesExactSpringfieldAsset → ⊥
networkSaleDoesNotCreateExactSpringfieldAsset ()

lobbyingMeetingDoesNotCreateGasAsk : LobbyingMeetingImpliesGasAsk → ⊥
lobbyingMeetingDoesNotCreateGasAsk ()

planMeetingDoesNotCreateDecisionOutcome : SpringfieldPlanMeetingImpliesDecisionOutcome → ⊥
planMeetingDoesNotCreateDecisionOutcome ()

substantialHoldingDoesNotCreateOperationalControl : SubstantialHoldingImpliesOperationalControl → ⊥
substantialHoldingDoesNotCreateOperationalControl ()

publicInfrastructureDoesNotCreatePrivateSubsidyAmount : PublicInfrastructureImpliesPrivateSubsidyAmount → ⊥
publicInfrastructureDoesNotCreatePrivateSubsidyAmount ()

parcelSaleDoesNotCreateMasterControlTransfer : ParcelSaleImpliesMasterControlTransferred → ⊥
parcelSaleDoesNotCreateMasterControlTransfer ()

------------------------------------------------------------------------
-- Recomputed residual Pareto after this receipt round.
------------------------------------------------------------------------

data ResidualCut : Set where
  cityWestLenderSecurityPackage : ResidualCut
  springfieldExactGasAssetSchedule : ResidualCut
  santoroDocumentsAndSpecificAsks : ResidualCut
  mirvacOriginal2002Instrument : ResidualCut
  currentMasterDeveloperCadastralRights : ResidualCut
  blackRockFundAndVotingDecomposition : ResidualCut
  projectSpecificInfrastructureIncidence : ResidualCut
  sameParcelValueEcologyJoin : ResidualCut

record ResidualPriority : Set where
  constructor residual-priority
  field
    cut : ResidualCut
    priority : Nat
    sameObjectRequired : Bool
    instruction : String
open ResidualPriority public

canonicalResidualCuts : List ResidualPriority
canonicalResidualCuts =
  residual-priority cityWestLenderSecurityPackage 100 true
    "Acquire title/mortgage/PPSR/company or financing records for the Gordon Springfield West Unit Trust / Springfield BJM Landlord Trust partnership: lender, secured party, equity split, guarantees and development facility."
  ∷ residual-priority springfieldExactGasAssetSchedule 100 true
    "Acquire the 2004 Energex-Springfield alliance instrument plus asset/easement schedules and the 2006 Allgas sale schedules sufficient to identify exact Springfield mains/service assets through the later GDI/Stonepeak chain."
  ∷ residual-priority santoroDocumentsAndSpecificAsks 99 true
    "Acquire lobbyist register client entries, briefing papers, correspondence, meeting notes and decision traces for the 2025 Springfield/Santoro meetings; distinguish general city-plan advocacy from gas, planning, health, finance or infrastructure asks."
  ∷ residual-priority mirvacOriginal2002Instrument 98 true
    "Acquire the August 2002 Orion acquisition/development agreement and title history to identify Springfield-side counterparty, price, retained rights, covenants and any revenue-sharing/JV terms."
  ∷ residual-priority currentMasterDeveloperCadastralRights 98 true
    "Build a current parcel-rights map of Springfield City Group retained land, sold land, options, JVs and continuing revenue/reversionary interests, starting with City West and Vantage."
  ∷ residual-priority blackRockFundAndVotingDecomposition 97 true
    "Resolve the 303,997,515 Mirvac securities across BlackRock entities/funds/mandates and voting authority; aggregate substantial holding is not a control theorem."
  ∷ residual-priority projectSpecificInfrastructureIncidence 96 true
    "Join Infrastructure Charges Notices/register entries, offsets/refunds, public road/rail spending and private contributions to the relevant Springfield parcels and quantify who pays versus who captures uplift."
  ∷ residual-priority sameParcelValueEcologyJoin 95 true
    "Join parcel-level market/development value and infrastructure benefit to Woogaroo/Springview clearing, offset, heat, water, traffic and connectivity burdens using exact cadastral/project geometry."
  ∷ []
