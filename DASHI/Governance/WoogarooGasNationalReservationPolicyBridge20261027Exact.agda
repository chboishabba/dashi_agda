module DASHI.Governance.WoogarooGasNationalReservationPolicyBridge20261027Exact where

-- Source-first ONE-WAY consumer of EXISTING Woogaroo, Springfield gas,
-- Australian gas-policy and genealogy owners. Nothing in this module asserts
-- that national LNG export gas reaches one de-identified Springfield dwelling.
-- Original producers: Parliament/ministerial speakers, Hanson/One Nation,
-- Senex/Darren Stevenson, AEMC, ABC, Energex/Springfield cited spokespersons.
-- Author of independent research framing: Johl Brown; OpenAI ChatGPT assisted
-- source audit and adaptation. No attribution of political direction to
-- a gas-network beneficiary absent actual commissioned work or decision joins.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.ClimateGenealogyTypedCasesExact as Gas
import DASHI.Governance.TypedGenealogyEdgeExact as Typed
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Woogaroo
import DASHI.Law.SensibLawAzureSpringfieldInducedGasDemandExact as Azure
import DASHI.Law.SensibLawSpringfieldResidentialGasEndpointLockInExact as Endpoint
import DASHI.Law.SensibLawSpringfieldFirstNineApprovalGasEndpointBridgeExact as Approval

------------------------------------------------------------------------
-- REUSE ACTUAL SOURCE OWNERS -- not duplicate facts or higher authority.
------------------------------------------------------------------------

reservationIntroducedOriginalOwner : Typed.TypedGenealogyEdge
reservationIntroducedOriginalOwner = Gas.octoberGasBillsIntroduced2026

levyWordCollisionOriginalOwner :
  INF.NonFactorabilityWitness Gas.displayedLevyWord Gas.legalBaseOfLevy
levyWordCollisionOriginalOwner = Gas.sameLevyWordDifferentLegalBases

historicalSpringfieldAlliance : Source.AttributedSource
historicalSpringfieldAlliance = Woogaroo.springfieldGasAllianceReport

actualAllgasNetworkLevelOwnership : Source.AttributedSource
actualAllgasNetworkLevelOwnership = Azure.allgasCurrentOwnership

deidentifiedEndpointEvidence : Azure.DeveloperEndpointIdentity
deidentifiedEndpointEvidence = Azure.azureDwellingIdentityObservation

unpaidNetworkRevenueAmount : Azure.DemandHypothesis
unpaidNetworkRevenueAmount = Azure.networkUtilisationResidual

-- The original 2018 First Nine EPBC approval is project/holder evidence ONLY.
-- Its operative terms do not establish a developer gas scheme or lobbying.
originalFirstNineNoGasPromotion : Approval.ApprovalIdentityBridge
originalFirstNineNoGasPromotion = Approval.firstNineSpringfieldIdentityBridge

------------------------------------------------------------------------
-- ORIGINAL PUBLISED OR MINISTER-REPORTED SOURCE OBJECTS.
-- Party policy, a minister's oral explanation, lobby response, and
-- a later source are different producers/objects. Web mirrors aren't
-- multiple independent original parliamentary proceedings.
------------------------------------------------------------------------

data GasSourceRole : Set where
  parliamentarySpeechMirror : GasSourceRole
  firstPartyPolicyStatement : GasSourceRole
  originalProducerResponse : GasSourceRole
  governmentOriginalRelease : GasSourceRole
  networkRegulatorOriginal : GasSourceRole
  contemporaneousInterviewReport : GasSourceRole

record ScopedGasReceipt : Set where
  constructor scoped-gas-receipt
  field
    producer : String
    date : String
    locator : String
    role : GasSourceRole
    scopeAndCeiling : String
open ScopedGasReceipt public

hansonMarch15ProductionMotion : ScopedGasReceipt
hansonMarch15ProductionMotion = scoped-gas-receipt
  "Senator Pauline Hanson, original Senate motion; OpenAustralia Hansard mirror"
  "2026-03-12"
  "https://www.openaustralia.org.au/senate/?id=2026-03-12.16.1"
  parliamentarySpeechMirror
  "Motion asked Commonwealth to subject ALL GAS PRODUCTION to 15% minimum domestic reserve; motion debate and voting are not a binding gas-reservation Act. Distinct from her March private bill's offshore exported-petroleum baseline. Murray Watt moved debate procedure; his floor role is not assent or privately directed gas policy."

hansonMarchPrivateBill : ScopedGasReceipt
hansonMarchPrivateBill = scoped-gas-receipt
  "Senator Pauline Hanson, Offshore Petroleum and Greenhouse Gas Storage Amendment (Domestic Reserve) Bill 2026; bill status via original parliamentary index / tracked bill"
  "2026-03-10"
  "https://opax.com.au/bill/au-federal-s1489"
  parliamentarySpeechMirror
  "Private senator's introduced bill would require domestic reserve agreement for 15% of EXPORTED petroleum from Commonwealth waters. Indexed tracker is not the native Act and the proposal is not enacted; this denominator/geography differs from 12 March motion all-production language."

hansonMayPolicyPivot : ScopedGasReceipt
hansonMayPolicyPivot = scoped-gas-receipt
  "Pauline Hanson, first-person May 21 gas-industry conference launch reported by ABC (Jacob Greber)"
  "2026-05-21"
  "https://www.abc.net.au/news/2026-05-21/one-nation-proposes-new-tax-break-for-drilling/106707250"
  contemporaneousInterviewReport
  "Party leader publicly moved away from compulsory gas export levy/reserve to future exploration incentives, optional state participation and new wellhead-royalty approach, grandfathering existing PRRT; acknowledged consulting industry but NAMED consultation source/tasking or signed agreement not established."

oneNationJuneOriginalPolicy : ScopedGasReceipt
oneNationJuneOriginalPolicy = scoped-gas-receipt
  "Pauline Hanson's One Nation, original party publisher"
  "2026-06-09"
  "https://www.onenation.org.au/gas-policy-ownership"
  firstPartyPolicyStatement
  "Party-authored policy rejects 25% export-value tax and compulsory 20% government reservation; advocates prospective 30% exploration rebate paired with up-to-30% Commonwealth equity option, wellhead royalty for new projects and investment vehicle. Own retrospective statement that industry was consulted: no named Senex/Hancock instruction or donor identity."

senexMayReservationObjection : ScopedGasReceipt
senexMayReservationObjection = scoped-gas-receipt
  "Senex Energy, CEO Darren Stevenson"
  "2026-05-08"
  "https://senexenergy.com.au/news/statement-on-domestic-gas-reservation-policy/"
  originalProducerResponse
  "First-party objection to proposed domestic reservation, argues risks to domestic-focused investment; independent public policy stance not proof Hanson copied/received its text and not same-object evidence of regulatory change."

senexSeptemberDetailedSubmission : ScopedGasReceipt
senexSeptemberDetailedSubmission = scoped-gas-receipt
  "Senex Energy, original exposure-draft response"
  "2026-09-24"
  "https://senexenergy.com.au/news/exposure-draft-domestic-gas-reservation-scheme-legislative-package/"
  originalProducerResponse
  "Public, explicitly scoped response to three federal exposure-draft Bills, asks up-to-20% be a ceiling, multi-year demand calibration and future supply protection; cannot retroactively cause earlier 10 September draft or 21 May party launch; no same-object clause adopted in Parliament shown."

fedOctober2026Package : ScopedGasReceipt
fedOctober2026Package = scoped-gas-receipt
  "Chris Bowen, Madeleine King, Tim Ayres, original Australian Government"
  "2026-10-14"
  "https://minister.dcceew.gov.au/bowen/media-releases/joint-media-release-landmark-legislation-secure-australian-gas-industry-and-households"
  governmentOriginalRelease
  "Three linked bills INTRODUCED 14 Oct 2026: LNG export-volume domestic obligation calibrated to demand, staged operation; no signed final statute, executed duty, price effect or individual Springfield beneficiary."

fedOctoberRegulatoryLicenceLevy : ScopedGasReceipt
fedOctoberRegulatoryLicenceLevy = scoped-gas-receipt
  "Madeleine King, original Commons ministerial second-reading; attributed OpenAustralia mirror"
  "2026-10-14"
  "https://www.openaustralia.org.au/debates/?id=2026-10-14.6.1"
  parliamentarySpeechMirror
  "Domestic Gas Reservation Levy Bill 2026 is proposed export LICENCE COST-RECOVERY by future regulation, NOT a proposed 25% export SALES ad valorem tax, nor a tax amount yet assessed or recovered."

aemcAllgasMarch2026 : ScopedGasReceipt
aemcAllgasMarch2026 = scoped-gas-receipt
  "Australian Energy Market Commission, original public pipeline register"
  "2026-03"
  "https://www.aemc.gov.au/energy-system/gas/gas-pipeline-register/qld-allgas-gas-distribution-network"
  networkRegulatorOriginal
  "Network-level Allgas Energy owned Stonepeak, AGIG operator following March 2026 GDI sale; former GDI 40% Marubeni / 40% SAS Trustee / 20% APA; Allgas distribution network covers south of Brisbane River. Does NOT itself establish an exact Azure home's MIRN, transport tariff, gas supplier, export-linked LNG chain or ultimate Springfield project profits."

------------------------------------------------------------------------
-- TYPE DISTINCTIONS. No conversion from upstream EXPORT LICENCE or from
-- downstream GAS SERVICE to a particular regulatory/beneficiary claim.
------------------------------------------------------------------------

data GasSystemLayer : Set where
  exportLicensing : GasSystemLayer
  domesticWholesaleProduction : GasSystemLayer
  localDistributionAsset : GasSystemLayer
  householdRetailService : GasSystemLayer
  housingDeveloperInclusion : GasSystemLayer

data DistinctGasObject : Set where

exportLicenceNotLocalDistributionAsset :
  exportLicensing ≡ localDistributionAsset → DistinctGasObject
exportLicenceNotLocalDistributionAsset ()

distributionAssetNotDeveloperContract :
  localDistributionAsset ≡ housingDeveloperInclusion → DistinctGasObject
distributionAssetNotDeveloperContract ()

data GasPolicyDenominator : Set where
  allProductionVolume : GasPolicyDenominator
  exportedOffshorePetroleumVolume : GasPolicyDenominator
  lngAnnualExportVolume : GasPolicyDenominator
  lngExportSalesValue : GasPolicyDenominator
  exportLicenceAdministrationCosts : GasPolicyDenominator

data GasPercentHeadline : Set where
  printedFifteenPercent : GasPercentHeadline

data March15PolicyObject : Set where
  offshoreBill15Exports : March15PolicyObject
  marchMotion15Production : March15PolicyObject

march15Printed : March15PolicyObject → GasPercentHeadline
march15Printed _ = printedFifteenPercent

march15LegalBase : March15PolicyObject → GasPolicyDenominator
march15LegalBase offshoreBill15Exports = exportedOffshorePetroleumVolume
march15LegalBase marchMotion15Production = allProductionVolume

same15DifferentDenominators :
  INF.NonFactorabilityWitness march15Printed march15LegalBase
same15DifferentDenominators =
  INF.nonFactorabilityWitness
    offshoreBill15Exports marchMotion15Production refl (λ ())

samePrinted15DoesNotIdentifyLegalBase :
  INF.FactorsThrough march15Printed march15LegalBase → ⊥
samePrinted15DoesNotIdentifyLegalBase =
  INF.witnessRulesOutEveryFlatFactorisation same15DifferentDenominators

data SourceReportedPoliticalStatus : Set where
  parliamentaryMotion : SourceReportedPoliticalStatus
  introducedBill : SourceReportedPoliticalStatus
  partyPolicyPublication : SourceReportedPoliticalStatus
  producerConsultationSubmission : SourceReportedPoliticalStatus
  enactedBindingAct : SourceReportedPoliticalStatus
  executedSupplyOrMeasuredEffect : SourceReportedPoliticalStatus

introducedIsNotAssented :
  introducedBill ≡ enactedBindingAct → DistinctGasObject
introducedIsNotAssented ()

partyPivotIsNotCommencedSupply :
  partyPolicyPublication ≡ executedSupplyOrMeasuredEffect → DistinctGasObject
partyPivotIsNotCommencedSupply ()

record WoogarooGasPolicyBoundary : Set where
  constructor woogaroo-gas-policy-boundary
  field
    original2004InfrastructureAllianceReported : Bool
    currentAllgasNetworkLevelStonepeakOwnerDocumented : Bool
    localExactMIRNDistributorAndRetailerAuthenticated : Bool
    upstreamLNGMoleculeToLocalConnectionMatched : Bool
    fixedAndThroughputNetworkTariffPossible : Bool
    endpointSpecificRevenueMeasured : Bool
    originalMarch15ReservePositionRecorded : Bool
    MayJuneOneNationPivotOriginalPublisherPresent : Bool
    SenexMayAndSeptemberPolicyResponsePresent : Bool
    SenexHancockToHansonExactOriginalPolicyInstructionVerified : Bool
    introducedOctoberFederalPackageDocumented : Bool
    signedAndCommencedFederalSchemeVerified : Bool
    federalCostRecoveryLevyIs25PctExportValueTax : Bool
    SpringfieldLobbyistMeetingSubjectGasPaid : Bool
    measurableWoogarooBenefitCausedByFederalPolicy : Bool
open WoogarooGasPolicyBoundary public

canonicalWoogarooGasPolicyBoundary : WoogarooGasPolicyBoundary
canonicalWoogarooGasPolicyBoundary = woogaroo-gas-policy-boundary
  true true false false true false true true true false true false false false false

noSpecificGasLobbyingPaid :
  SpringfieldLobbyistMeetingSubjectGasPaid canonicalWoogarooGasPolicyBoundary ≡ false
noSpecificGasLobbyingPaid = refl

noLocalMoleculeTransferPaid :
  upstreamLNGMoleculeToLocalConnectionMatched canonicalWoogarooGasPolicyBoundary ≡ false
noLocalMoleculeTransferPaid = refl

noHancockSenexPartyTaskPaid :
  SenexHancockToHansonExactOriginalPolicyInstructionVerified canonicalWoogarooGasPolicyBoundary ≡ false
noHancockSenexPartyTaskPaid = refl

noPriceOutcomeProven :
  measurableWoogarooBenefitCausedByFederalPolicy canonicalWoogarooGasPolicyBoundary ≡ false
noPriceOutcomeProven = refl

-- Remaining original-object acquisition:
-- (a) official individual MIRN/distributor contract and tariffs, redacted;
-- (b) actual AGIG/Allgas network cost/usage allocation and physical footprint;
-- (c) amendment provenance and identified lobbying submissions/instructions;
-- (d) 2026 federal bill vote/assent and 2028 implementation; (e) time series
-- of household/industrial domestic wholesale prices with matched controls.
