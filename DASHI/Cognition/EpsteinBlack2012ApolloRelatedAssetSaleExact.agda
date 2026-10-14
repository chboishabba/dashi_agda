module DASHI.Cognition.EpsteinBlack2012ApolloRelatedAssetSaleExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 2012 BLACK FAMILY PARTNERS / FINANCIAL TRUST ASSET-SALE BRIDGE
--
-- Primary records now distinguish three stages:
--   * an early unsigned draft carrying an approximately USD18m package price;
--   * a late-November closing sequence repriced to USD5.5m;
--   * a Nov-28 final allocation email: ESWW USD5m, AP SHL USD250k,
--     AP Technology USD250k, followed by a Nov-30 USD5,500,030 bank credit.
--
-- Repricing is a paid chronology; its reason is not yet paid.
------------------------------------------------------------------------

data SaleAsset : Set where
  environmentalSolutionsWorldwide : SaleAsset
  apSHLInvestors : SaleAsset
  apTechnologyPartners : SaleAsset

data SaleEvidenceClass : Set where
  fileInventory : SaleEvidenceClass
  earlyDraftAgreement : SaleEvidenceClass
  finalAllocationEmail : SaleEvidenceClass
  transferInstrument : SaleEvidenceClass
  processedBankCredit : SaleEvidenceClass
  laterBuyerAccounting : SaleEvidenceClass

record SaleReceipt : Set where
  constructor sale-receipt
  field
    label : String
    source : String
    evidenceClass : SaleEvidenceClass
    boundedFinding : String
    amountUSD : Nat
    executionPaid : Bool
    finalAllocationPaid : Bool
    apolloCorporateTransactionPaid : Bool
open SaleReceipt public

closingInventoryReceipt : SaleReceipt
closingInventoryReceipt = sale-receipt
  "Financial Trust closing-file inventory"
  "EFTA00299927 / EFTA00299930 inventory family"
  fileInventory
  "The released records inventory a Black Family Partners purchase from Financial Trust of ESWW, AP SHL Investors and AP Technology Partners, with purchase/sale agreement, allocations, consents, assignments, stock powers and wire instructions."
  0 false false false

early18mDraft : SaleReceipt
early18mDraft = sale-receipt
  "Early November USD18m draft package"
  "EFTA00586106"
  earlyDraftAgreement
  "An unsigned early-November draft assigns an aggregate purchase price around USD18m across ESWW, AP SHL and AP Technology. It is a draft state only and is superseded by the later closing-price/allocation evidence."
  18000000 false false false

finalAllocationNov28 : SaleReceipt
finalAllocationNov28 = sale-receipt
  "28 November USD5.5m final allocation email"
  "EFTA00693690..93"
  finalAllocationEmail
  "Darren Indyke forwarded an allocation received from Eileen Alexanderson stating: USD5m ESWW shares, USD250k AP SHL interest and USD250k AP Technology interest, explicitly described as allocation of the USD5.5m purchase price. A 2014 basis inquiry independently refers back to these amounts as the sale prices used."
  5500000 true true false

processed5500030Credit : SaleReceipt
processed5500030Credit = sale-receipt
  "30 November 2012 BFP -> Financial Trust bank credit"
  "EFTA01510783 / duplicate EFTA01510763"
  processedBankCredit
  "Financial Trust's JPMorgan record shows a USD5,500,030 CHIPS credit from Black Family Partners LP from Bank of America in the closing window. The USD30 excess over the documented USD5.5m allocation remains unexplained and is not relabelled as a fee."
  5500030 true true false

eswwTransferMechanics : SaleReceipt
eswwTransferMechanics = sale-receipt
  "ESWW stock-transfer mechanics"
  "EFTA00585846 and related closing instruments"
  transferInstrument
  "Closing materials include a stock power for 13,198,711 ESWW shares and a separate transfer instruction for 151,494 broker-held shares, together matching Financial Trust's 13,350,205-share block."
  0 false false false

blackFamilyApolloRelatedClassification : SaleReceipt
blackFamilyApolloRelatedClassification = sale-receipt
  "Black-family AP SHL/AP Technology classification"
  "EFTA00590400 / EFTA00602764"
  laterBuyerAccounting
  "Black-family investment materials classify AP Technology Partners and AP SHL Investors as 'Apollo Related Entities' while separately identifying Apollo funds/co-invest vehicles. This pays Apollo adjacency, not an Apollo corporate purchase or Apollo-managed-fund transfer."
  0 true false false

record SaleRepricing : Set where
  constructor sale-repricing
  field
    earlyDraftUSD : Nat
    closingAllocationUSD : Nat
    processedCreditUSD : Nat
    repricingPaid : Bool
    repricingReasonPaid : Bool
    priceChangeImpliesImpropriety : Bool
open SaleRepricing public

canonicalSaleRepricing : SaleRepricing
canonicalSaleRepricing = sale-repricing 18000000 5500000 5500030 true false false

record FinalAllocation : Set where
  constructor final-allocation
  field
    eswwUSD : Nat
    apSHLUSD : Nat
    apTechnologyUSD : Nat
    aggregateUSD : Nat
open FinalAllocation public

canonicalFinalAllocation : FinalAllocation
canonicalFinalAllocation = final-allocation 5000000 250000 250000 5500000

record SaleBoundary : Set where
  constructor sale-boundary
  field
    bfpPaidFinancialTrust5500030 : Bool
    assetPackageDocumentFamilyExists : Bool
    finalAllocationPaid : Bool
    apSHLAndAPTechnologyApolloRelated : Bool
    apSHLAndAPTechnologyApolloManagedFunds : Bool
    fullySignedFinalAgreementLocated : Bool
    saleWasApolloCorporateTransaction : Bool
    2012WireWasAdvisoryFee : Bool
    repricingReasonPaid : Bool
open SaleBoundary public

canonicalSaleBoundary : SaleBoundary
canonicalSaleBoundary = sale-boundary
  true true true true false false false false false

data ApolloRelatedImpliesApolloFund : Set where
data BFPBuyerImpliesApolloBuyer : Set where
data DraftPriceImpliesClosingPrice : Set where
data RepricingImpliesImpropriety : Set where
data SalePaymentImpliesAdvisoryFee : Set where

apolloRelatedDoesNotCreateApolloFund : ApolloRelatedImpliesApolloFund → ⊥
apolloRelatedDoesNotCreateApolloFund ()

bfpBuyerDoesNotCreateApolloBuyer : BFPBuyerImpliesApolloBuyer → ⊥
bfpBuyerDoesNotCreateApolloBuyer ()

draftPriceDoesNotCreateClosingPrice : DraftPriceImpliesClosingPrice → ⊥
draftPriceDoesNotCreateClosingPrice ()

repricingDoesNotCreateImpropriety : RepricingImpliesImpropriety → ⊥
repricingDoesNotCreateImpropriety ()

salePaymentDoesNotCreateAdvisoryFee : SalePaymentImpliesAdvisoryFee → ⊥
salePaymentDoesNotCreateAdvisoryFee ()

record PaymentClassificationCorrection : Set where
  constructor payment-classification-correction
  field
    senateSecondFilingFlags2012Wire : Bool
    sameAmountAssetSaleReceiptExists : Bool
    countingWireAsServiceFeeIsPaid : Bool
    senate170mTransactionTotalEqualsDechertServiceFeeTotal : Bool
open PaymentClassificationCorrection public

canonicalPaymentClassificationCorrection : PaymentClassificationCorrection
canonicalPaymentClassificationCorrection = payment-classification-correction true true false false

data SaleDebt : Set where
  executedSaleAgreement : SaleDebt
  repricingRationale : SaleDebt
  bofaDebitAdvice : SaleDebt
  eswwTransferAgentCompletion : SaleDebt
  apSHLConsentAndPostSaleRights : SaleDebt
  apTechnologyConsentAndPostSaleRights : SaleDebt
  economicGainLossReconstruction : SaleDebt

record SaleAcquisition : Set where
  constructor sale-acquisition
  field
    debt : SaleDebt
    priority : Nat
    question : String
open SaleAcquisition public

canonicalSaleAcquisition : List SaleAcquisition
canonicalSaleAcquisition =
  sale-acquisition repricingRationale 100
    "Explain the change from the early USD18m draft to the USD5.5m closing allocation through valuation workpapers, negotiations, tax/accounting advice or contemporaneous correspondence; chronology alone does not explain motive."
  ∷ sale-acquisition executedSaleAgreement 100
    "Acquire the final fully executed purchase-and-sale agreement and compare its terms with the Nov-28 allocation email and Nov-30 settlement."
  ∷ sale-acquisition bofaDebitAdvice 99
    "Acquire the Bank of America debit advice and explain the USD30 excess over the documented purchase allocation."
  ∷ sale-acquisition eswwTransferAgentCompletion 99
    "Resolve ESWW shareholder-register/transfer-agent completion and subsequent ownership."
  ∷ sale-acquisition apSHLConsentAndPostSaleRights 98
    "Acquire final AP SHL assignment/member consent and trace rights/value after Black Family Partners became holder."
  ∷ sale-acquisition apTechnologyConsentAndPostSaleRights 98
    "Acquire final AP Technology assignment/member consent and trace rights/value after transfer."
  ∷ sale-acquisition economicGainLossReconstruction 97
    "Reconstruct Financial Trust's original cost, distributions and sale proceeds asset-by-asset before computing gain or loss."
  ∷ []
