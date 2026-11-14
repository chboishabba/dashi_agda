module DASHI.Law.SensibLawWoogarooSecondThirdOrderIncidenceBridge20261027Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawWoogarooGainLossSnowballAdapterExact as GainLoss
import DASHI.Law.SensibLawWoogarooPostApprovalPoliticalGasBenefit20261027Exact as Post
import DASHI.Law.SensibLawWoogarooAttachmentSameObjectAudit20261027Exact as Attachment

------------------------------------------------------------------------
-- SECOND / THIRD-ORDER BENEFIT INCIDENCE — A THIN CANONICAL LAW CONSUMER
--
-- Reuses the already-merged gain/loss distribution and post-approval owners.
-- Companion Cognition PR #1131 already developed layered Springfield value
-- capture, public infrastructure, Orion/Mirvac, BlackRock, City West and
-- gas-network inference. Its particular source authorship and prior methods
-- remain attributed. That open draft is a ONE-WAY methodological donor:
-- no import, duplicate general ontology, or fake independent evidence root.
--
-- Incidence is not intent. An option is not realised income. A shareholder
-- of a nearby different company is not a Cherish/Stockland counterparty.
-- An historic public concession is not a newly accrued 2026 project subsidy.
------------------------------------------------------------------------

-- Explicitly consumed prior owners; no new general distribution framework.
priorLocalPlanningOption : GainLoss.DistributionCoordinate
priorLocalPlanningOption = GainLoss.developerPrecinctOption

priorEconomicIncidenceDebt : GainLoss.DistributionResidual
priorEconomicIncidenceDebt = GainLoss.whoCapturesDevelopmentValue

currentFederalGate : Post.ScopedReceipt
currentFederalGate = Post.developmentRegulatoryGate

priorIndexedOwnerConsent : Attachment.ScopedClaim
priorIndexedOwnerConsent = Attachment.separateConsentDocumentsOnlyIndexed

data Order : Set where
  firstOrderDirect : Order
  secondOrderIndirect : Order
  thirdOrderInducedOrFinancial : Order

data Mechanism : Set where
  developmentOption : Mechanism
  housingNarrative : Mechanism
  infrastructureChargeLiability : Mechanism
  infrastructureCostTransfer : Mechanism
  historicConcessionalCredit : Mechanism
  connectedGasDemand : Mechanism
  retailRentOrLandOption : Mechanism
  securityholderEconomicExposure : Mechanism
  corridorLossExternality : Mechanism

data EvidenceTier : Set where
  sourceSpecificOriginal : EvidenceTier
  originalIndexedNotFaceChecked : EvidenceTier
  firstPartyClaim : EvidenceTier
  historicalOriginal : EvidenceTier
  boundedCounterfactual : EvidenceTier
  currentTransactionOpen : EvidenceTier

data TimeScope : Set where
  historical1994 : TimeScope
  historical2005 : TimeScope
  review2013to2018 : TimeScope
  localDA2024to2025 : TimeScope
  federalApproval2026 : TimeScope
  potentialPost2026 : TimeScope

qcaSpringfieldAssistance : Source.AttributedSource
qcaSpringfieldAssistance = Source.mkNoDOISource
  "Queensland Competition Authority"
  "Industry Assistance in Queensland 2015 — Volume II: Springfield Loan Agreement"
  "Queensland Treasury original-hosted 2015 QCA report"
  "2015"
  "https://s3.treasury.qld.gov.au/files/Industry-Assistance-in-Queensland-2015-Final-Report-Volume-2.pdf"
  Source.governmentSource
  "2015 QCA original PDF text indexed by public search but publisher-hosted PDF returned 403 on direct open. Table says 1994 agreement, outstanding developer contribution due by creation of 10000 Greater Springfield residential allotments, CPI rather than higher market bond interest, and total 313000 AUD modelled assistance 2013-2018 only. Neither current loan balance nor Springview-specific subsidy or cash payment verified; independent physical report face still needed."
  Source.publicAttribution

parliament2005Gas : Source.AttributedSource
parliament2005Gas = Source.mkNoDOISource
  "Queensland Legislative Assembly"
  "Energy Legislation Amendment Bill debate — 27 October 2005"
  "Queensland parliamentary original Hansard, PDF page index 65"
  "27 October 2005"
  "https://documents.parliament.qld.gov.au/events/han/2005/2005_10_27_WEEKLY.pdf"
  Source.governmentSource
  "Original official Hansard text retrieved; page 65 says Energex via Allgas planned Springfield gas network expansion; publisher screenshot request timed out. This pays historic network identity/planned rollout, not present parcel pipe assets, accomplished connections, 2026 licence ownership or revenue."
  Source.publicAttribution

councilCharges2025 : Source.AttributedSource
councilCharges2025 = Source.mkNoDOISource
  "Ipswich City Council"
  "Infrastructure Planning — 2025 adopted charges and 2026 guidance"
  "Ipswich council original infrastructure-charging rules"
  "2025–2026"
  "https://www.ipswich.qld.gov.au/Services/Planning-and-Building/Planning/Infrastructure-Planning/Infrastructure-Planning"
  Source.governmentSource
  "Council levies road, parks and land-for-community-facilities trunk infrastructure charges; Urban Utilities water/sewerage charges are in separate notices. ICNs attach to land and are payable by owner at payment time; abatements, offsets, refunds, infrastructure agreements and deferrals must be established by same-lot documents. 2025 resolution supersedes 2024 for prospective rate rules; do not silently re-rate old ICNs at 2025 levels."
  Source.publicAttribution

councilVillage2ChargeIndex : Source.AttributedSource
councilVillage2ChargeIndex = Source.mkNoDOISource
  "Ipswich City Council"
  "4272/2020/ADP Village 2 28 June 2024 Infrastructure Charges Notice"
  "Council original indexed document entry"
  "28 June 2024"
  "https://edoc.ipswich.qld.gov.au/objective/?env=iccecm&id=1011265&plat=pwy"
  Source.governmentSource
  "Original file index lists a 520.5KB 28 June 2024 charge notice, plus council signed decision, SARA and approved plans. Index pays its EXISTENCE, NOT line-item amount, offsets, exemptions, actual payments or infrastructure delivered."
  Source.publicAttribution

councilVillage3ChargeIndex : Source.AttributedSource
councilVillage3ChargeIndex = Source.mkNoDOISource
  "Ipswich City Council"
  "5547/2020/ADP Village 3 14 May 2025 Infrastructure Charges Notice"
  "Council original indexed document entry"
  "14 May 2025"
  "https://edoc.ipswich.qld.gov.au/objective/?env=iccecm&id=1029140&plat=pwy"
  Source.governmentSource
  "Original file index lists a 514.69KB 14 May 2025 charge notice and related approvals. Existence does not pay net project charge, amount paid, grant or public/private incidence."
  Source.publicAttribution

mirvac2026Orion : Source.AttributedSource
mirvac2026Orion = Source.mkNoDOISource
  "Mirvac"
  "Orion Springfield Central — property portfolio FY26"
  "Mirvac original commercial investment-property disclosure"
  "30 June 2026"
  "https://www.mirvac.com/investor-centre/property-portfolio/retail/orion-springfield-central"
  Source.practitionerSource
  "Mirvac itself reports Orion Springfield Central 100 percent owned, 518 million AUD directors' valuation at 30 June 2026 including sundry vacant land, and August 2002 acquisition/agreement date. Different retail/land asset from Cherish Village 2/3 parcels. Gross Orion valuation is NOT Woogaroo uplift and says nothing about original 2002 contract counterparty rights."
  Source.publicAttribution

mirvac2026Annual : Source.AttributedSource
mirvac2026Annual = Source.mkNoDOISource
  "Mirvac"
  "Mirvac Group Annual Report 2026"
  "Mirvac first-party investor reporting index and report"
  "19 August 2026"
  "https://www.mirvac.com/investor-centre/annual-report"
  Source.practitionerSource
  "First-party index for FY26 annual report. Indexed FY26 holdings schedule reports BlackRock Group 303997515 securities / 7.70 percent as at a 2 April 2026 notice (third-party textual mirror also available). Aggregate security interest is NOT ownership of Springfield City Group, beneficial ownership of Springview, BlackRock policy instruction, or direct share of any particular Orion rent."
  Source.publicAttribution

record IncidencePath : Set where
  constructor incidence-path
  field
    order : Order
    mechanism : Mechanism
    source : Source.AttributedSource
    tier : EvidenceTier
    time : TimeScope
    benefitedOrExposedActor : String
    sourcePaidStatement : String
    contingentNextEdge : String
    sourceLevelValueOrOptionIdentified : Bool
    actualNetTransferPaid : Bool
    actualNetTransferPaidIsFalse : actualNetTransferPaid ≡ false

open IncidencePath public

directApprovalEntitlement : IncidencePath
directApprovalEntitlement = incidence-path
  firstOrderDirect developmentOption Post.approvalNotice sourceSpecificOriginal federalApproval2026
  "Cherish proponent / relevant third-party landholder and Stockland developer under separate rights"
  "15 October 2026 EPBC project approval with conditions reduces a Commonwealth regulatory hurdle, not other statutory conditions or risks."
  "Executed developer/deed options, signed approval and true land titles determine who can exercise/sell entitlement and when."
  true false refl

politicalHousingPolicyNarrative : IncidencePath
politicalHousingPolicyNarrative = incidence-path
  secondOrderIndirect housingNarrative Post.housingRelease sourceSpecificOriginal federalApproval2026
  "Commonwealth Government and Labor housing-policy communications, NOT Watt's personal account"
  "Original pre-approval housing-throughput release provides documented policy frame, no proof of inclusion or attribution to specific October approval."
  "Exact dated post-15 October government account or KPI identifies whether and how Springview was counted; constructed vs planned must differ."
  false false refl

cityInfrastructureCharge : IncidencePath
cityInfrastructureCharge = incidence-path
  firstOrderDirect infrastructureChargeLiability councilVillage2ChargeIndex originalIndexedNotFaceChecked localDA2024to2025
  "current title owner as statutorily charged, Ipswich Council recipient subject to offsets"
  "Original 2024 Village 2 charge-notice existence in Council index, separate from new 2025 maximum-charge rate resolution."
  "Open actual signed ICN, each amount, due date, paid balance, offset/refund and legal owner; do not infer charge receipts from an index."
  false false refl

waterSewerChargeFork : IncidencePath
waterSewerChargeFork = incidence-path
  secondOrderIndirect infrastructureCostTransfer councilCharges2025 sourceSpecificOriginal potentialPost2026
  "landowner, Ipswich Council and Urban Utilities on SEPARATE infrastructure instruments"
  "Council's publicly stated current charging system directs water/sewerage charges to Urban Utilities, not necessarily the Ipswich ICN."
  "Same-project UU ICN/offset/works agreement and who ultimately bore costs; rates/capital uplift cannot be inferred."
  false false refl

historicSpringfieldCredit : IncidencePath
historicSpringfieldCredit = incidence-path
  secondOrderIndirect historicConcessionalCredit qcaSpringfieldAssistance originalIndexedNotFaceChecked review2013to2018
  "Springfield Land Corporation and Queensland public treasury under a historic 1994 framework"
  "QCA estimated 313000 AUD of assistance in its 2013-2018 measured/projected period from CPI versus market interest on a conditional infrastructure contribution."
  "Signed 1994 instrument, actual payment dates, current outstanding balance and whether Cherish/Springview are contractually relevant must be established separately."
  true false refl

historicGasExpansion : IncidencePath
historicGasExpansion = incidence-path
  secondOrderIndirect connectedGasDemand parliament2005Gas historicalOriginal historical2005
  "Energex/Allgas historical planned network; actual current Springview distributor/retailer unknown"
  "Original 2005 Queensland Hansard reports intention to extend gas network to Greater Springfield; no site-specific 2026 supply or revenue measured."
  "Georeferenced pipe maps, 2026 supplier quotes, meter installations, asset continuity and all-electric comparator."
  false false refl

orionRetailRentsAndExpansion : IncidencePath
orionRetailRentsAndExpansion = incidence-path
  thirdOrderInducedOrFinancial retailRentOrLandOption mirvac2026Orion firstPartyClaim potentialPost2026
  "Mirvac direct ownership of Orion, separate from Cherish/Stockland and Springfield master-developer"
  "As at June 2026 Mirvac attributes 518m AUD portfolio valuation to Orion (including sundry vacant land); current retail/rental asset exposure is source-paid."
  "Causal uplift from Woogaroo decision requires before/after comparable valuations and explicit incremental footfall or infrastructure effects; no project transfer assumed."
  true false refl

listedEquityExposure : IncidencePath
listedEquityExposure = incidence-path
  thirdOrderInducedOrFinancial securityholderEconomicExposure mirvac2026Annual originalIndexedNotFaceChecked potentialPost2026
  "BlackRock-group funds as Mirvac listed-security holders; not direct Springview owners"
  "2026 Mirvac annual report locates 303997515 securities, 7.70 percent of issued stapled securities for BlackRock as a disclosed substantial holder."
  "A specific fund, voting mandate, asset-level return, period and causal connection to Woogaroo are required; never multiply 7.70 percent by Orion gross value to claim cash benefit."
  true false refl

matureCorridorCost : IncidencePath
matureCorridorCost = incidence-path
  thirdOrderInducedOrFinancial corridorLossExternality Attachment.councilVillage3Approval sourceSpecificOriginal potentialPost2026
  "affected habitat/corridor users and public ecological estate, not abstract market owners"
  "Existence of Village 3 ADP and federal approval creates legally relevant land-use pressure, but actual post-approval habitat loss is not measured."
  "Exact clearing event/polygon, ecological baseline, mature-tree habitat and offset realisation; public cost cannot be set to zero from lack of market price."
  false false refl

layeredIncidencePaths : List IncidencePath
layeredIncidencePaths =
  directApprovalEntitlement ∷
  politicalHousingPolicyNarrative ∷
  cityInfrastructureCharge ∷
  waterSewerChargeFork ∷
  historicSpringfieldCredit ∷
  historicGasExpansion ∷
  orionRetailRentsAndExpansion ∷
  listedEquityExposure ∷
  matureCorridorCost ∷ []

record NetIncidenceRequirements : Set where
  constructor net-incidence-requirements
  field
    identityAndSameParcel : Bool
    transactionOrRegulatoryAmount : Bool
    legalPaymentOrExerciseTiming : Bool
    projectCounterfactual : Bool
    fullCostAndBenefitAllocation : Bool
    verifiedRealisation : Bool

-- An UNSATISFIED minimum bundle, not a witness of proven project economics.
currentNetIncidencePayment : NetIncidenceRequirements
currentNetIncidencePayment = net-incidence-requirements
  false false false false false false

------------------------------------------------------------------------
-- Live minimal acquisition cut, prioritised by decision-changing ability.
-- Scores route work; they are not probabilities, evidentiary grades or
-- valuations. Source material can arrive out-of-order but never pays a
-- missing dependency simply by proximity or chronology.
------------------------------------------------------------------------

data IncidenceDebt : Set where
  signedFederalDecisionAndCounsel : IncidenceDebt
  exactCouncilVillage2And3ChargeNotices : IncidenceDebt
  signedCherishStocklandTitleDeed : IncidenceDebt
  current1994LoanAccountAndTenKTrigger : IncidenceDebt
  sameAsset2026GasMeterAndDistributor : IncidenceDebt
  orionCounterfactualAndFundExposure : IncidenceDebt
  sameParcelEcologicalOffsetAndPublicSpend : IncidenceDebt

record IncidenceCut : Set where
  constructor incidence-cut
  field
    debt : IncidenceDebt
    sourceAcquisitionPriority : String
    livePublicSource : Bool
    presentPayment : Bool
    exactlyMissing : String
    noNameOnlyShortcut : Bool
    noNameOnlyShortcutIsTrue : noNameOnlyShortcut ≡ true

open IncidenceCut public

canonicalIncidenceCuts : List IncidenceCut
canonicalIncidenceCuts =
  incidence-cut signedFederalDecisionAndCounsel "P0 LEGAL" true false
    "Signed 15 Oct approval with operative conditions and reasons; statutory filing/standing/restraint counsel immediately."
    true refl ∷
  incidence-cut exactCouncilVillage2And3ChargeNotices "P1 AMOUNT" true false
    "Original 2024 Village 2 and 2025 Village 3 ICN PDF faces, payment/offset record and distinct Urban Utilities ICNs. Indexed files exist but direct download failed."
    true refl ∷
  incidence-cut signedCherishStocklandTitleDeed "P1 RIGHTS" false false
    "Current title, June 2023 indexed owner/developer consent faces, developer option/finance agreements and who has actual sale proceeds."
    true refl ∷
  incidence-cut current1994LoanAccountAndTenKTrigger "P2 HISTORY" false false
    "Actual historic 1994 loan deed, later repayment balances and status of 10000 cumulative Greater Springfield allotment trigger; no ratio from proposed 1838 Springview lots."
    true refl ∷
  incidence-cut sameAsset2026GasMeterAndDistributor "P2 PHYSICAL" false false
    "2026 site-specific gas asset and network provider, installation and tariff contract, plus all-electric comparison."
    true refl ∷
  incidence-cut orionCounterfactualAndFundExposure "P3 FINANCE" false false
    "Causally attributable incremental Orion rent/land uplift with date-control group, actual BlackRock fund and cash-flow allocation; no percent-of-gross-value shortcut."
    true refl ∷
  incidence-cut sameParcelEcologicalOffsetAndPublicSpend "P1 BURDEN" true false
    "Actual clearing envelope/sequence, conservation conditions, paid offsets, council and Urban Utilities infrastructure delivery, public burden and counterfactual."
    true refl ∷ []

data HistoricQCAWindowEqualsPostApprovalSubsidy : Set where
data Citywide10000AllotmentsEqualsTwoADPs1838Lots : Set where
data ListedNoticeEqualsPaidInfrastructureCharges : Set where
data InfrastructureChargeEqualsWaterSewerCharge : Set where
data Pre2026OrionValuationEqualsWoogarooUplift : Set where
data MirvacBlackRockHoldingMeansSpringviewControl : Set where
data HistoricalAllgasPlanEqualsPresentRevenue : Set where
data HousingPolicyBenefitMeansMinisterPersonalBenefit : Set where
data ApprovalMeansCompletedHousingOrClearing : Set where

historicAssistanceNotNew2026Grant :
  HistoricQCAWindowEqualsPostApprovalSubsidy → ⊥
historicAssistanceNotNew2026Grant ()

citywideThresholdNotTwoVillas :
  Citywide10000AllotmentsEqualsTwoADPs1838Lots → ⊥
citywideThresholdNotTwoVillas ()

indexNotPaidCharge : ListedNoticeEqualsPaidInfrastructureCharges → ⊥
indexNotPaidCharge ()

uuSeparateFromCityCharge : InfrastructureChargeEqualsWaterSewerCharge → ⊥
uuSeparateFromCityCharge ()

orionValuationNotWoogarooUplift :
  Pre2026OrionValuationEqualsWoogarooUplift → ⊥
orionValuationNotWoogarooUplift ()

blackRockHoldingNotParcelControl :
  MirvacBlackRockHoldingMeansSpringviewControl → ⊥
blackRockHoldingNotParcelControl ()

gasPlanNotCurrentRevenue : HistoricalAllgasPlanEqualsPresentRevenue → ⊥
gasPlanNotCurrentRevenue ()

politicalBenefitNotPersonalGain :
  HousingPolicyBenefitMeansMinisterPersonalBenefit → ⊥
politicalBenefitNotPersonalGain ()

approvalNotRealisation : ApprovalMeansCompletedHousingOrClearing → ⊥
approvalNotRealisation ()
