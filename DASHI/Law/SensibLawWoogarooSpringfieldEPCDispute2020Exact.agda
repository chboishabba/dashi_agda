{-# OPTIONS --safe #-}
module DASHI.Law.SensibLawWoogarooSpringfieldEPCDispute2020Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Law.SensibLawWoogarooSpringfield2020CompetitivePlanningTransmission20261030Exact as Policy
import DASHI.Law.SensibLawWoogarooSpringfieldStatutoryInfrastructureGate20261030Exact as Law
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Gas
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Ibrahim
import DASHI.Wikimedia.IdentifierExact as Identifier
import DASHI.Law.SensibLawWoogaroo9281NegotiatedApprovedGeometryExact as CouncilGeometry

------------------------------------------------------------------------
-- 2020 CHERISH / SPRINGFIELD CITY GROUP EPC CONTRACTUAL DISPUTE
--
-- ORIGINAL INDEPENDENT SPEAKERS: (1) Cherish / Samuel and Johnson Lin,
-- assisted by Stephen Fynes-Clinton, and (2) SCG / Russell Luhrs.
-- Sources are 15 June 2020 parliamentary transcript and Cherish's original
-- supplementary 19 June letter. A quoted 8m AUD request was DISPUTED and
-- NOT a receipt of an actual charge, payment, enrichment or illegality.
-- The 4000 EP capacity discussion was about WATER / SEWER, specifically
-- Opossum Creek trunk sewer, not reticulated fossil GAS.
-- The separate 2004/2005 Springfield natural gas network is not this asset.
------------------------------------------------------------------------

qld2020Hearing : Source.AttributedSource
qld2020Hearing = Source.mkNoDOISource
  "Queensland Parliament, State Development Tourism Innovation and Manufacturing Committee"
  "Public Hearing: Forest Wind Farm Development Bill 2020, original Hansard transcript, pages 15-16 and 33-34"
  "Original parliamentary oral-evidence transcript"
  "15 June 2020"
  "https://documents.parliament.qld.gov.au/Committees/SDTIMC/2020/ForestWindFarmDB20/trns-ph-15Jun2020.pdf"
  Source.governmentSource
  "Records Cherish Johnson Lin firsthand testimony of alleged 4000 equivalent-person capacity at 2000 AUD/EP (8m AUD) and Cherish's O'Dwyer Creek trunk sewer/wildlife corridor claims. Independently records SCG Russell Luhrs disputing double dipping, describing 4000 EP reserved within water/sewer network, and possible extra sewer capacity on Opossum Creek trunk sewer subject to compensation; no original bills, transfer, tender or payment receipts."
  Source.publicAttribution

cherish19JuneSupplement : Source.AttributedSource
cherish19JuneSupplement = Source.mkNoDOISource
  "Samuel Lin / Cherish Enterprises Pty Ltd; assisted Johnson Lin and Stephen Fynes-Clinton"
  "Supplementary Information on Planning Act amendments, infrastructure credits and EP credits"
  "Original Cherish-authored submission to Queensland parliamentary committee"
  "19 June 2020"
  "https://documents.parliament.qld.gov.au/com/SDTIMC-C65A/RN156PFWFD-45DA/cor-19Jun2020.pdf"
  Source.practitionerSource
  "Original 8 page signed/dated Cherish correspondence. Quotes 1998 Springfield Infrastructure Agreement clause numbers (26.5, 43, 67, 86, 95.4, 118, 130.4, 151, 163.5, 172), asserts 2008 2000 AUD/EPC proposal, alleges lack of transparent price mechanism/setoff and third-party examples, acknowledges uncertain water/sewer credits and conflicting testimony. Neither signed SIA, invoice, demand letter nor any payment authenticated."
  Source.publicAttribution

disputedEPCAtlas : Source.AttributedSourceAtlas
disputedEPCAtlas = Source.mkSourceAtlas
  "Springfield Opossum Creek sewer EPCs and disputed infrastructure charges 2020"
  "DASHI.Law.SensibLawWoogarooSpringfieldEPCDispute2020Exact"
  (qld2020Hearing ∷ cherish19JuneSupplement ∷
   Law.springfieldStructurePlan2025 ∷ [])
  "One parliamentary hearing carrier reports independently attributed oral speakers, but is not evidence of execution. Cherish follow-up is the same party's extra source, not a second independent complainant."

data UtilityKind : Set where
  trunkSewerCapacity : UtilityKind
  waterSupplyCapacity : UtilityKind
  roadInfrastructureCredits : UtilityKind
  openSpaceFacilityCredits : UtilityKind
  reticulatedFossilGas : UtilityKind

data ClaimPosition : Set where
  cherishPaymentToRegainPlanningSupport : ClaimPosition
  scgExtraCapacityCostRecovery : ClaimPosition
  unverifiedOtherDeveloperEPCCharges : ClaimPosition

data EvidentiaryStatus : Set where
  firstPartyHearingTestimony : EvidentiaryStatus
  firstPartySupplementStatement : EvidentiaryStatus
  paidTransactionReceipt : EvidentiaryStatus
  independentlyAdjudicated : EvidentiaryStatus

record DisputedTransferClaim : Set where
  constructor disputed-transfer-claim
  field
    source : Source.AttributedSource
    claim : ClaimPosition
    utility : UtilityKind
    grade : EvidentiaryStatus
    quantityEP : Nat
    unitPriceAUD : Nat
    allegedAggregateAUD : Nat
    originalInvoicePaid : Bool
    paymentMadeProved : Bool
    courtFoundMisconduct : Bool
open DisputedTransferClaim public

cherishAlleged2008Price : DisputedTransferClaim
cherishAlleged2008Price = disputed-transfer-claim
  qld2020Hearing
  cherishPaymentToRegainPlanningSupport
  trunkSewerCapacity
  firstPartyHearingTestimony
  4000 2000 8000000
  false false false

scgAlternativeCapacityAccount : DisputedTransferClaim
scgAlternativeCapacityAccount = disputed-transfer-claim
  qld2020Hearing
  scgExtraCapacityCostRecovery
  trunkSewerCapacity
  firstPartyHearingTestimony
  4000 0 0
  false false false

-- Pure arithmetic on reported parameters: not a debt/invoice/payments proof.
cherishHypotheticalPriceMath : 4000 * 2000 ≡ 8000000
cherishHypotheticalPriceMath = refl

data WaterSewerAsset : Set where
  odwyerCreekTrunkSewer : WaterSewerAsset
  opossumCreekTrunkSewer : WaterSewerAsset

data GasAsset : Set where
  allgasSpringfieldDistribution : GasAsset

record ContestedInfrastructureClaim : Set where
  constructor contested-infrastructure-claim
  field
    source : Source.AttributedSource
    attributedSpeaker : String
    statement : String
    sameAssetContractPaid : Bool
    measuredOutlayPaid : Bool
    actualPartyPaymentPaid : Bool

cherishOdwyerSewerClaim : ContestedInfrastructureClaim
cherishOdwyerSewerClaim = contested-infrastructure-claim
  qld2020Hearing
  "Johnson Lin, Cherish hearing testimony, 15 June 2020"
  "Cherish says it constructed first trunk sewer known as O'Dwyer Creek trunk sewer at its own cost; contributed toward major roads and restructuring of wildlife corridor. These are oral claims, not same-parcel project works receipts."
  false false false

scgOpossumNetworkClaim : ContestedInfrastructureClaim
scgOpossumNetworkClaim = contested-infrastructure-claim
  qld2020Hearing
  "Russell Luhrs, SCG hearing testimony, 15 June 2020"
  "SCG says 4000 EP capacity was preserved for Cherish in water/sewer network and extra capacity would need cost reimbursement, describes 21m AUD Opossum Creek trunk sewer network duplication. No actual invoiced charges, expenditure audit or 2019/8575 same-lot link."
  false false false

record AgreementClauseLocator : Set where
  constructor agreement-clause-locator
  field
    clause : String
    allegedCreditSubject : String
    originalSigned1998DeedFacePaid : Bool

agreementCreditLocators : List AgreementClauseLocator
agreementCreditLocators =
  agreement-clause-locator "26.5" "regional road works" false ∷
  agreement-clause-locator "43" "developer and Council road works" false ∷
  agreement-clause-locator "67,86" "Council external water infrastructure" false ∷
  agreement-clause-locator "95.4,118" "Council external sewerage infrastructure" false ∷
  agreement-clause-locator "130.4,151" "open space dedication" false ∷
  agreement-clause-locator "163.5,172" "community facilities" false ∷ []

-- Distinct *utility type* even if all infrastructure is in the same region.
data SewerIsGas : Set where

differentUtilityTypes : SewerIsGas → ⊥
differentUtilityTypes ()

-- A historical offer about sewer network capacity is compatible with both
-- actual payment and no payment. It cannot imply that a specific transfer
-- occurred, even where the alleged unit-price arithmetic is correct.
data PaymentWorld : Set where
  priceQuotedNoTransfer : PaymentWorld
  priceQuotedWithDifferentPaymentReceipt : PaymentWorld

data SameQuotedPrice : Set where
  quoted4000EPAt2000AUD : SameQuotedPrice

data TransferReceipt : Set where
  noActualTransferDocument : TransferReceipt
  originalBankOrReceiptPaid : TransferReceipt

priceObservation : PaymentWorld → SameQuotedPrice
priceObservation priceQuotedNoTransfer = quoted4000EPAt2000AUD
priceObservation priceQuotedWithDifferentPaymentReceipt = quoted4000EPAt2000AUD

paidTransfer : PaymentWorld → TransferReceipt
paidTransfer priceQuotedNoTransfer = noActualTransferDocument
paidTransfer priceQuotedWithDifferentPaymentReceipt = originalBankOrReceiptPaid

differentPaymentStatus :
  paidTransfer priceQuotedNoTransfer ≡
  paidTransfer priceQuotedWithDifferentPaymentReceipt → ⊥
differentPaymentStatus ()

quotedEPCPriceDoesNotProvePayment :
  INF.FactorsThrough priceObservation paidTransfer → ⊥
quotedEPCPriceDoesNotProvePayment =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness priceQuotedNoTransfer
      priceQuotedWithDifferentPaymentReceipt refl differentPaymentStatus)

-- The public conflict is authentic as testimony. Competing explanations
-- are not a proof of which narrative is correct or any improper motive.
data CauseWorld : Set where
  planningConsistencyObjection : CauseWorld
  financialCapacityCondition : CauseWorld

data HearingObservation : Set where
  twoConflictingOriginalSpeakers : HearingObservation

data HistoricalCauseEstablished : Set where
  lackOfRetailPlanConsistency : HistoricalCauseEstablished
  allegedPaymentCondition : HistoricalCauseEstablished

heardBoth : CauseWorld → HearingObservation
heardBoth planningConsistencyObjection = twoConflictingOriginalSpeakers
heardBoth financialCapacityCondition = twoConflictingOriginalSpeakers

actualReason : CauseWorld → HistoricalCauseEstablished
actualReason planningConsistencyObjection = lackOfRetailPlanConsistency
actualReason financialCapacityCondition = allegedPaymentCondition

differentReason :
  actualReason planningConsistencyObjection ≡
  actualReason financialCapacityCondition → ⊥
differentReason ()

competingTestimonyDoesNotAdjudicateCausation :
  INF.FactorsThrough heardBoth actualReason → ⊥
competingTestimonyDoesNotAdjudicateCausation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness planningConsistencyObjection
      financialCapacityCondition refl differentReason)

-- Existing Ibrahim/QID route provides searchable law category, not a
-- Wikidata person/entity identity or an authenticated contract.
legalNavigationQid : Identifier.ItemId
legalNavigationQid = Ibrahim.environmentalLawQid

data HighestAlphaPayment : Set where
  signed1998SIAWithAmendments : HighestAlphaPayment
  alleged2008EPCDemandLetter : HighestAlphaPayment
  originalSCGQUUServicingAgreement : HighestAlphaPayment
  CherishEPsAndMasterPlan : HighestAlphaPayment
  councilAdoptedChargesAndCredits : HighestAlphaPayment
  actualTransferAndReceiptLedger : HighestAlphaPayment
  siteParcelAndCreekGeometry : HighestAlphaPayment
  current20198575GasServicingSchedule : HighestAlphaPayment

orderedEvidenceCuts : List HighestAlphaPayment
orderedEvidenceCuts =
  signed1998SIAWithAmendments ∷
  alleged2008EPCDemandLetter ∷
  originalSCGQUUServicingAgreement ∷
  CherishEPsAndMasterPlan ∷
  councilAdoptedChargesAndCredits ∷
  actualTransferAndReceiptLedger ∷
  siteParcelAndCreekGeometry ∷
  current20198575GasServicingSchedule ∷ []

------------------------------------------------------------------------
-- 2020 Opossum Creek historic trunk sewer vs 2026 Council EXTERNAL SEWER
-- Reuse the original stamped 9281 geometry carrier, not a copied plan index.
------------------------------------------------------------------------

approved2026CouncilExternalSewer : CouncilGeometry.ApprovedPlanCarrierReceipt
approved2026CouncilExternalSewer = CouncilGeometry.negotiated9281ApprovedPlans

historical2020HearingCarrier : Source.AttributedSource
historical2020HearingCarrier = qld2020Hearing

-- Both source objects mention the Opossum Creek / O'Dwyer corridor, but
-- different dates and asset descriptions cannot pay exact pipeline identity.
data SewerCorridorWorld : Set where
  twoDistinctSewerAssetSegments : SewerCorridorWorld
  samePipeEstablishedByMissingAsBuilt : SewerCorridorWorld

data SharedCreekName : Set where
  namedOpossumOdwyerArea : SharedCreekName

data ActualSewerSegmentIdentity : Set where
  pipelineIdentityStillOpen : ActualSewerSegmentIdentity
  exactGeoreferencedPipeIdentityPaid : ActualSewerSegmentIdentity

observedSharedCreek : SewerCorridorWorld → SharedCreekName
observedSharedCreek twoDistinctSewerAssetSegments = namedOpossumOdwyerArea
observedSharedCreek samePipeEstablishedByMissingAsBuilt = namedOpossumOdwyerArea

pipelineIdentity : SewerCorridorWorld → ActualSewerSegmentIdentity
pipelineIdentity twoDistinctSewerAssetSegments = pipelineIdentityStillOpen
pipelineIdentity samePipeEstablishedByMissingAsBuilt = exactGeoreferencedPipeIdentityPaid

distinctPipeIdentity :
  pipelineIdentity twoDistinctSewerAssetSegments ≡
  pipelineIdentity samePipeEstablishedByMissingAsBuilt → ⊥
distinctPipeIdentity ()

creekNameAndApprovedWorksDoNotIdentifyHistoricPipe :
  INF.FactorsThrough observedSharedCreek pipelineIdentity → ⊥
creekNameAndApprovedWorksDoNotIdentifyHistoricPipe =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness twoDistinctSewerAssetSegments
      samePipeEstablishedByMissingAsBuilt refl distinctPipeIdentity)

data PipeAcquisitionTarget : Set where
  council9281ApprovedExternalSewerCAD : PipeAcquisitionTarget
  quuAsBuilt2020ExistingTrunkSewer : PipeAcquisitionTarget
  1998SIAAndCurrentSewerServicingAgreements : PipeAcquisitionTarget
  2026ParcelAndStageGeometry : PipeAcquisitionTarget
  sameActionAndPrestartEvidence : PipeAcquisitionTarget

samePipePareto : List PipeAcquisitionTarget
samePipePareto =
  council9281ApprovedExternalSewerCAD ∷
  quuAsBuilt2020ExistingTrunkSewer ∷
  1998SIAAndCurrentSewerServicingAgreements ∷
  2026ParcelAndStageGeometry ∷
  sameActionAndPrestartEvidence ∷ []


------------------------------------------------------------------------
-- Exact 2023 Council index anchors, one carrier not independent receipts.
-- 292 is the Applicant's 2023 Sewer and Water Masterplan attachment;
-- 321 is a separately indexed Remittance Advice, NOT a payment receipt.
------------------------------------------------------------------------

record CouncilIndexedPotentialJoin : Set where
  constructor council-indexed-potential-join
  field
    source : Source.AttributedSource
    councilApplication : String
    fileIndex : String
    indexedFileLabel : String
    underlyingFaceReceived : Bool
    actualCashTransferProved : Bool

springview2023SewerWaterMasterplanLocator : CouncilIndexedPotentialJoin
springview2023SewerWaterMasterplanLocator = council-indexed-potential-join
  Law.councilSpringviewIndex
  "6243/2023/LAP"
  "292 (3 Oct 2023)"
  "Applicant response to information request - Appendix A - Sewer and Water Masterplan"
  false false

springview2023RemittanceAdviceLocator : CouncilIndexedPotentialJoin
springview2023RemittanceAdviceLocator = council-indexed-potential-join
  Law.councilSpringviewIndex
  "6243/2023/LAP"
  "321 (29 Jun 2023)"
  "Application Supporting Information - Remittance Advice"
  false false

-- A council file index label alone cannot tell whether the remittance
-- concerned an application fee, any third-party transaction, or neither.
data IndexedAdviceWorld : Set where
  adviceIndexedForApplicationAdmin : IndexedAdviceWorld
  adviceIndexedWithIndependentlyVerifiedTransfer : IndexedAdviceWorld

data AdviceLabel : Set where
  remittanceAdviceOnlyIndexed : AdviceLabel

data TransferDisposition : Set where
  noUnderlyingPaymentAuthenticated : TransferDisposition
  verifiedTransferAndBeneficiary : TransferDisposition

adviceIndex : IndexedAdviceWorld → AdviceLabel
adviceIndex adviceIndexedForApplicationAdmin = remittanceAdviceOnlyIndexed
adviceIndex adviceIndexedWithIndependentlyVerifiedTransfer = remittanceAdviceOnlyIndexed

adviceDisposition : IndexedAdviceWorld → TransferDisposition
adviceDisposition adviceIndexedForApplicationAdmin = noUnderlyingPaymentAuthenticated
adviceDisposition adviceIndexedWithIndependentlyVerifiedTransfer = verifiedTransferAndBeneficiary

differentDisposition :
  adviceDisposition adviceIndexedForApplicationAdmin ≡
  adviceDisposition adviceIndexedWithIndependentlyVerifiedTransfer → ⊥
differentDisposition ()

remittanceAdviceIndexDoesNotEstablishBeneficiaryPayment :
  INF.FactorsThrough adviceIndex adviceDisposition → ⊥
remittanceAdviceIndexDoesNotEstablishBeneficiaryPayment =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness adviceIndexedForApplicationAdmin
      adviceIndexedWithIndependentlyVerifiedTransfer refl differentDisposition)
