module DASHI.Cognition.EpsteinYLKAssetReturnLifecycle20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinCOUQYLKAssetTransfer20261015Exact as Transfer
import DASHI.Cognition.EpsteinWexnerCOUQFungibleCapitalLifecycle20261015Exact as Origin

------------------------------------------------------------------------
-- YLK ASSET-RETURN LIFECYCLE — 2026-10-15
--
-- Filed tax-return transfer facts are kept separate from the later
-- Wexner-commissioned review's provenance/restitution characterization.
------------------------------------------------------------------------

data YLKSourceClass : Set where
  filedTaxReturn : YLKSourceClass
  foundationCommissionedReview : YLKSourceClass
  publicWexnerStatement : YLKSourceClass

record YLKReceipt : Set where
  constructor ylk-receipt
  field
    label : String
    dateOrYear : String
    sourceClass : YLKSourceClass
    source : String
    boundedFinding : String
    amountUSD : Nat
    transactionPaid : Bool
    restitutionCharacterizationPaid : Bool
open YLKReceipt public

couqContribution2008 : YLKReceipt
couqContribution2008 = ylk-receipt
  "COUQ noncash contribution to YLK" "2008" filedTaxReturn
  "YLK 2008 Schedule B, EIN 26-1605864"
  "YLK's filed Schedule B reports a noncash contribution of USD12,377,844 from The C.O.U.Q. Foundation."
  12377844 true false

ftcContribution2008 : YLKReceipt
ftcContribution2008 = ylk-receipt
  "Financial Trust noncash contribution to YLK" "2008" filedTaxReturn
  "YLK 2008 Schedule B, EIN 26-1605864"
  "YLK's filed Schedule B reports a noncash contribution of USD34,280,154 from Financial Trust Company. The later foundation review identifies this as 201,939 Apple shares; the Schedule B amount/entity is independently paid by the return."
  34280154 true false

record InitialYLKCapitalization : Set where
  constructor initial-ylk-capitalization
  field
    couqUSD : Nat
    ftcUSD : Nat
    combinedUSD : Nat
    bothNoncash : Bool
open InitialYLKCapitalization public

canonicalInitialYLKCapitalization : InitialYLKCapitalization
canonicalInitialYLKCapitalization = initial-ylk-capitalization
  12377844 34280154 46657998 true

wfcfReceipt2010 : YLKReceipt
wfcfReceipt2010 = ylk-receipt
  "YLK dissolution transfer to Wexner Family Charitable Fund — 2010 tranche" "2010" filedTaxReturn
  "Wexner Family Charitable Fund 2010 Form 990-PF, Attachment 8"
  "The recipient foundation reports USD33,310,678 of assets transferred from YLK under a plan of dissolution."
  33310678 true false

wfcfReceipt2011 : YLKReceipt
wfcfReceipt2011 = ylk-receipt
  "YLK dissolution transfer to Wexner Family Charitable Fund — 2011 tranche" "2011" filedTaxReturn
  "Wexner Family Charitable Fund 2011 Form 990-PF, Attachment 10"
  "The recipient foundation reports a further USD1,831,006 of assets transferred from YLK under a plan of dissolution."
  1831006 true false

record DissolutionTransfer : Set where
  constructor dissolution-transfer
  field
    tranche2010USD : Nat
    tranche2011USD : Nat
    filedCombinedUSD : Nat
open DissolutionTransfer public

canonicalDissolutionTransfer : DissolutionTransfer
canonicalDissolutionTransfer = dissolution-transfer 33310678 1831006 35141684

reviewAppleIdentification : YLKReceipt
reviewAppleIdentification = ylk-receipt
  "Independent-review Apple-share identification" "2020" foundationCommissionedReview
  "Wexner Foundation independent review, 24 Feb 2020"
  "The foundation-commissioned review identifies FTC's USD34,280,154 YLK contribution as 201,939 Apple shares and calculates the combined COUQ+FTC book-value transfer at USD46,657,998."
  34280154 false false

reviewRestitutionCharacterization : YLKReceipt
reviewRestitutionCharacterization = ylk-receipt
  "Partial-recovery characterization" "2020" foundationCommissionedReview
  "Wexner Foundation independent review, relying on Wexner statements/interviews and foundation/tax records"
  "The review accepts Leslie and Abigail Wexner's account that the assets transferred to YLK represented partial recovery of assets misappropriated from the Wexner family. This pays an attributed institutional-review conclusion, not an adjudicated tracing or restitution judgment."
  0 false true

record YLKBoundary : Set where
  constructor ylk-boundary
  field
    initialFiledTransferPaid : Bool
    dissolutionFiledTransferPaid : Bool
    combinedInitialUSD : Nat
    combinedDissolutionUSD : Nat
    reviewSaysPartialRecovery : Bool
    reviewConclusionIsCourtAdjudication : Bool
    initialMinusDissolutionEqualsLoss : Bool
    everyYLKAssetWasWexnerOriginPaidByTaxReturns : Bool
    appleSharesProveWexnerBeneficialOwnership : Bool
open YLKBoundary public

canonicalYLKBoundary : YLKBoundary
canonicalYLKBoundary = ylk-boundary
  true true 46657998 35141684 true false false false false

data ReviewImpliesAdjudicatedRestitution : Set where
data TransferDifferenceImpliesEconomicLoss : Set where
data CharitableTransferImpliesPersonalOwnership : Set where

reviewDoesNotCreateAdjudicatedRestitution : ReviewImpliesAdjudicatedRestitution → ⊥
reviewDoesNotCreateAdjudicatedRestitution ()

transferDifferenceDoesNotCreateLoss : TransferDifferenceImpliesEconomicLoss → ⊥
transferDifferenceDoesNotCreateLoss ()

charitableTransferDoesNotCreatePersonalOwnership : CharitableTransferImpliesPersonalOwnership → ⊥
charitableTransferDoesNotCreatePersonalOwnership ()

------------------------------------------------------------------------
-- Max-cut: reconcile YLK's intervening economics and provenance.
------------------------------------------------------------------------

data YLKDebt : Set where
  full2008NoncashSchedule : YLKDebt
  ylkGrantInvestmentLedger2008to2011 : YLKDebt
  appleShareDisposition : YLKDebt
  couqTransferredAssetSchedule : YLKDebt
  dissolutionPlanAndClosingLedger : YLKDebt
  privateWexnerEpsteinSettlement : YLKDebt
  provenanceRestitutionReconciliation : YLKDebt

record YLKAcquisition : Set where
  constructor ylk-acquisition
  field
    debt : YLKDebt
    priority : Nat
    question : String
open YLKAcquisition public

canonicalYLKAcquisition : List YLKAcquisition
canonicalYLKAcquisition =
  ylk-acquisition privateWexnerEpsteinSettlement 100
    "Acquire the 2007/08 private settlement/recovery agreement and schedules before treating the charitable transfers as all, part or separate from any broader Wexner recovery." ∷
  ylk-acquisition ylkGrantInvestmentLedger2008to2011 100
    "Reconstruct YLK grants, investment gains/losses, expenses and distributions between USD46.658m initial book-value receipt and USD35.142m filed dissolution transfers; the difference is not automatically loss." ∷
  ylk-acquisition full2008NoncashSchedule 99
    "Acquire the complete YLK 2008 noncash-contribution schedules to identify every security/asset, basis and valuation supporting the two Schedule B aggregates." ∷
  ylk-acquisition appleShareDisposition 99
    "Trace the 201,939 Apple shares through sales, gains/losses and remaining dissolution assets using YLK investment schedules." ∷
  ylk-acquisition couqTransferredAssetSchedule 99
    "Reconcile the COUQ transfer's Bear ABS, Second City and other securities to the USD12.378m YLK tax-return aggregate without mixing valuation dates/bases." ∷
  ylk-acquisition dissolutionPlanAndClosingLedger 99
    "Acquire YLK's dissolution plan, final return and closing ledger and reconcile the 2010/2011 recipient-foundation tranches." ∷
  ylk-acquisition provenanceRestitutionReconciliation 98
    "Compare tax/bank/trust records against the Wexner-account and review characterization of returned/misappropriated assets without turning that characterization into an adjudicated fact."
  ∷ []
