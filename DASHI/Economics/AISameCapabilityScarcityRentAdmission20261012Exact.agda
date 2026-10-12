module DASHI.Economics.AISameCapabilityScarcityRentAdmission20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIQualityNormalizedPriceSpread20261012Exact as QualityPrice

------------------------------------------------------------------------
-- SAME-CAPABILITY SCARCITY-RENT ADMISSION
--
-- Cross-pollination from the scoped-verifier matched-pair evaluation protocol:
-- benchmark-normalised price comparison is not enough. Promotion to a scarcity-
-- rent claim requires a declared matched task/capability/accounting surface.
------------------------------------------------------------------------

record MatchedScarcityRentProtocol : Set where
  constructor matched-scarcity-rent-protocol
  field
    openModel : String
    closedModel : String
    sameBenchmarkFamily : Bool
    sameTaskSet : Bool
    sameToolAccess : Bool
    sameContextBudget : Bool
    sameComputeAccounting : Bool
    capabilityEquivalent : Bool
    apiPriceObserved : Bool
    providerMarginalCostObserved : Bool
    selectedPairAdmissibleForSameCapabilityRent : Bool
    selectedPairAdmissibleForProviderMargin : Bool

open MatchedScarcityRentProtocol public

mimoVsOpusAdmissionState : MatchedScarcityRentProtocol
mimoVsOpusAdmissionState = matched-scarcity-rent-protocol
  "MiMo-V2.6-Pro"
  "Claude Opus 5.5 Max"
  true
  true
  false
  false
  true
  false
  true
  false
  false
  false

selectedPairPriceReceiptPaid :
  QualityPrice.selectedPairClosed QualityPrice.mimoVsOpusBenchmarkPricePair ≡ true
selectedPairPriceReceiptPaid = QualityPrice.selectedPairIsPaid

selectedPairCapabilityMatchedIsFalse :
  capabilityEquivalent mimoVsOpusAdmissionState ≡ false
selectedPairCapabilityMatchedIsFalse = refl

selectedPairSameCapabilityRentAdmissionIsFalse :
  selectedPairAdmissibleForSameCapabilityRent mimoVsOpusAdmissionState ≡ false
selectedPairSameCapabilityRentAdmissionIsFalse = refl

selectedPairProviderMarginAdmissionIsFalse :
  selectedPairAdmissibleForProviderMargin mimoVsOpusAdmissionState ≡ false
selectedPairProviderMarginAdmissionIsFalse = refl

matchedScarcityRentAdmissionStillOpen : Bool
matchedScarcityRentAdmissionStillOpen = true

record SameCapabilityScarcityRentReceipt : Set₁ where
  constructor same-capability-scarcity-rent-receipt
  field
    protocol : MatchedScarcityRentProtocol
    capabilityMatchPaid : capabilityEquivalent protocol ≡ true
    taskMatchPaid : sameTaskSet protocol ≡ true
    toolAccessMatchPaid : sameToolAccess protocol ≡ true
    contextBudgetMatchPaid : sameContextBudget protocol ≡ true
    computeAccountingMatchPaid : sameComputeAccounting protocol ≡ true
    pricePaid : apiPriceObserved protocol ≡ true

open SameCapabilityScarcityRentReceipt public

-- No canonical SameCapabilityScarcityRentReceipt is supplied for the current
-- MiMo/Opus pair because capability/tool/context matching is not paid.

data BenchmarkNormalisationCreatesMatchedPair : Set where
data PriceGapCreatesProviderMargin : Set where
data OneMatchedPairCreatesGlobalScarcityRent : Set where

benchmarkNormalisationDoesNotCreateMatchedPair :
  BenchmarkNormalisationCreatesMatchedPair → ⊥
benchmarkNormalisationDoesNotCreateMatchedPair ()

priceGapDoesNotCreateProviderMargin : PriceGapCreatesProviderMargin → ⊥
priceGapDoesNotCreateProviderMargin ()

oneMatchedPairDoesNotCreateGlobalScarcityRent :
  OneMatchedPairCreatesGlobalScarcityRent → ⊥
oneMatchedPairDoesNotCreateGlobalScarcityRent ()

scarcityRentAdmissionBoundary : String
scarcityRentAdmissionBoundary =
  "The current MiMo/Opus price pair is source-paid and benchmark-normalised but not capability-matched. Same-capability scarcity-rent promotion requires matched task, tool access, context budget and compute accounting plus explicit capability equivalence. Provider margin separately requires same-object marginal serving cost."
