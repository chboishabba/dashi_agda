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
-- The November 2012 USD5.5m-class wire is not silently classified as an
-- advisory fee. Released inventory, draft closing materials and the receiving
-- bank record instead support an asset-sale package containing ESWW shares and
-- membership interests in AP SHL Investors and AP Technology Partners.
-- Black-family records classify AP SHL/AP Technology as Apollo-related
-- entities, while distinguishing them from Apollo funds/co-invest entities.
------------------------------------------------------------------------

data SaleAsset : Set where
  environmentalSolutionsWorldwide : SaleAsset
  apSHLInvestors : SaleAsset
  apTechnologyPartners : SaleAsset

data SaleEvidenceClass : Set where
  fileInventory : SaleEvidenceClass
  draftAgreement : SaleEvidenceClass
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
  "The released Financial Trust records inventory a 'Purchase & Sale by Black Family Partners, LP from Financial Trust Company, Inc.' of interests in Environmental Solutions Worldwide, AP SHL Investors LLC and AP Technology Partners LLC, with purchase/sale agreement, allocation schedule, consents, assignments, ESWW stock powers and wire instructions. Inventory proves the closing document family existed, not that every listed draft/instrument was fully executed."
  0 false false false

processed5500030Credit : SaleReceipt
processed5500030Credit = sale-receipt
  "30 November 2012 BFP -> Financial Trust bank credit"
  "EFTA01510783 / duplicate EFTA01510763"
  processedBankCredit
  "Financial Trust's JPMorgan record shows a USD5,500,030 CHIPS credit from Black Family Partners LP, sent from Bank of America originator account ending 0135, in the targeted closing window. The latest located sale-package drafts state an aggregate USD5.5m purchase price. The extra USD30 remains unexplained and is not labelled a fee."
  5500030 true false false

eswwTransferMechanics : SaleReceipt
eswwTransferMechanics = sale-receipt
  "ESWW stock-transfer mechanics"
  "EFTA00585846 and related closing-file instruments"
  transferInstrument
  "The closing materials include a stock power for 13,198,711 ESWW shares and a separate transfer instruction for 151,494 broker-held shares, together matching Financial Trust's 13,350,205-share block. This materially supports intended full-position transfer while leaving final transfer-agent completion to the shareholder/register record."
  0 false false false

blackFamilyApolloRelatedClassification : SaleReceipt
blackFamilyApolloRelatedClassification = sale-receipt
  "Black-family AP SHL/AP Technology classification"
  "EFTA00590400 / EFTA00602764 Black Family Group investment materials"
  laterBuyerAccounting
  "Black-family investment materials explicitly classify AP Technology Partners LLC and AP SHL Investors LLC as 'Apollo Related Entities' and separately classify Apollo funds/co-invest vehicles as Apollo entities. Later Black-family look-through records carry AP Technology/AP SHL positions. This pays Apollo adjacency/classification, not an Apollo corporate purchase or Apollo-managed-fund transfer."
  0 true false false

record SaleBoundary : Set where
  constructor sale-boundary
  field
    bfpPaidFinancialTrust5500030 : Bool
    assetPackageDocumentFamilyExists : Bool
    apSHLAndAPTechnologyApolloRelated : Bool
    apSHLAndAPTechnologyApolloManagedFunds : Bool
    finalExecutedAgreementLocated : Bool
    exactFinalAssetAllocationLocated : Bool
    saleWasApolloCorporateTransaction : Bool
    2012WireWasAdvisoryFee : Bool
open SaleBoundary public

canonicalSaleBoundary : SaleBoundary
canonicalSaleBoundary = sale-boundary
  true true true false false false false false

data ApolloRelatedImpliesApolloFund : Set where
data BFPBuyerImpliesApolloBuyer : Set where
data ProcessedWireImpliesEveryDraftTermFinal : Set where
data SalePaymentImpliesAdvisoryFee : Set where

apolloRelatedDoesNotCreateApolloFund : ApolloRelatedImpliesApolloFund → ⊥
apolloRelatedDoesNotCreateApolloFund ()

bfpBuyerDoesNotCreateApolloBuyer : BFPBuyerImpliesApolloBuyer → ⊥
bfpBuyerDoesNotCreateApolloBuyer ()

processedWireDoesNotFinalizeEveryDraft : ProcessedWireImpliesEveryDraftTermFinal → ⊥
processedWireDoesNotFinalizeEveryDraft ()

salePaymentDoesNotCreateAdvisoryFee : SalePaymentImpliesAdvisoryFee → ⊥
salePaymentDoesNotCreateAdvisoryFee ()

------------------------------------------------------------------------
-- Reconciliation significance.
------------------------------------------------------------------------

record PaymentClassificationCorrection : Set where
  constructor payment-classification-correction
  field
    senateSecondFilingFlags2012Wire : Bool
    sameAmountAssetSaleReceiptExists : Bool
    countingWireAsServiceFeeIsPaid : Bool
    senate170mTransactionTotalEqualsDechertServiceFeeTotal : Bool
open PaymentClassificationCorrection public

canonicalPaymentClassificationCorrection : PaymentClassificationCorrection
canonicalPaymentClassificationCorrection = payment-classification-correction
  true true false false

------------------------------------------------------------------------
-- Remaining acquisition.
------------------------------------------------------------------------

data SaleDebt : Set where
  executedSaleAgreement : SaleDebt
  finalAllocationSchedule : SaleDebt
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
  sale-acquisition executedSaleAgreement 100
    "Acquire the final signed purchase-and-sale agreement rather than treating draft agreement versions as operative."
  ∷ sale-acquisition finalAllocationSchedule 100
    "Resolve the final USD5.5m allocation among ESWW, AP SHL and AP Technology; draft allocations changed materially and cannot be promoted."
  ∷ sale-acquisition bofaDebitAdvice 99
    "Acquire the 30 November 2012 Bank of America debit advice for Black Family Partners account ending 0135 and explain the USD30 excess over the draft purchase price."
  ∷ sale-acquisition eswwTransferAgentCompletion 99
    "Resolve ESWW shareholder-register/transfer-agent completion and subsequent reverse-split ownership to close legal title transfer."
  ∷ sale-acquisition apSHLConsentAndPostSaleRights 98
    "Acquire final AP SHL assignment/member consent and trace rights/value after Black Family Partners became holder."
  ∷ sale-acquisition apTechnologyConsentAndPostSaleRights 98
    "Acquire final AP Technology assignment/member consent and trace rights/value after transfer."
  ∷ sale-acquisition economicGainLossReconstruction 97
    "Reconstruct Financial Trust's original cost, interim distributions and sale proceeds asset-by-asset before calling the USD5.5m package a gain or loss."
  ∷ []
