module DASHI.Economics.SoftBankOpenAIValuationLeverage2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIFinancingReflexivityExact as Reflexive

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    publisher : String
    date : String
    sourceLocation : String
    boundedProposition : String
    primarySource : Bool

open SourceReceipt public

followOnInvestment : SourceReceipt
followOnInvestment = sourceReceipt
  "SoftBank Group"
  "2026-02-27"
  "Follow-on Investments in OpenAI"
  "SoftBank agreed to invest an additional USD 30 billion in OpenAI at a USD 730 billion pre-money valuation; cumulative investment was expected to reach USD 64.6 billion and approximately 13 percent ownership."
  true

bridgeFacility : SourceReceipt
bridgeFacility = sourceReceipt
  "SoftBank Group"
  "2026-03-27"
  "Execution of Bridge Facility Agreement Primarily for the Follow-on Investments in OpenAI"
  "SoftBank entered a USD 40 billion bridge facility primarily to fund the OpenAI follow-on investment and general corporate purposes."
  true

firstTrancheBorrowing : SourceReceipt
firstTrancheBorrowing = sourceReceipt
  "SoftBank Group"
  "2026-04-01"
  "Execution of Follow-on Investment First Tranche"
  "SoftBank executed a USD 10 billion OpenAI investment tranche and stated that it borrowed USD 10 billion under the bridge facility to procure the required funds."
  true

record SoftBankOpenAIValuationLeverageCalibration : Set where
  constructor softBankOpenAIValuationLeverageCalibration
  field
    investmentReceipt : SourceReceipt
    bridgeReceipt : SourceReceipt
    borrowingReceipt : SourceReceipt
    largeValuationExposure : Bool
    investmentFinancedWithBorrowingAtFirstTranche : Bool
    valuationMarkIsExternalCustomerCash : Bool
    leverageProvesInvestmentInvalid : Bool
    openAIFutureCashFlowsValidateInvestment : Bool

canonicalSoftBankOpenAIValuationLeverageCalibration :
  SoftBankOpenAIValuationLeverageCalibration
canonicalSoftBankOpenAIValuationLeverageCalibration =
  softBankOpenAIValuationLeverageCalibration
    followOnInvestment bridgeFacility firstTrancheBorrowing
    true true false false false

markedGainDoesNotCloseExternalCash :
  Reflexive.Econ.MarkedGainImpliesExternalCashPermission → ⊥
markedGainDoesNotCloseExternalCash = Reflexive.markedGainDoesNotCloseExternalCash

data BorrowedInvestmentImpliesBubblePermission : Set where

borrowedInvestmentDoesNotAutoPromoteToBubble :
  BorrowedInvestmentImpliesBubblePermission → ⊥
borrowedInvestmentDoesNotAutoPromoteToBubble ()
