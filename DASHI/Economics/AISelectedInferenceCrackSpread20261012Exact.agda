module DASHI.Economics.AISelectedInferenceCrackSpread20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AISameModelSelfHostCostBoundary20261012Exact as SameModel

------------------------------------------------------------------------
-- SELECTED AI INFERENCE "CRACK SPREAD"
--
-- Oil crack spread compares a processed-output price with feedstock input cost.
-- The nearest source-paid AI analogue currently available in this tranche is a
-- BUYER-SIDE hosted-vs-self-host spread on the SAME model/configuration.
--
-- MiniMax-M3 under the declared RightNow-AI engineering configuration:
--   estimated self-host cost = 93 cents / million output tokens
--   hosted API price/cost    = 120 cents / million output tokens
--   selected hosting spread = 27 cents / million output tokens
--   spread / hosted price    = 22.5% = 2250 bp
--
-- This is not provider gross margin: the hosted provider's own marginal-cost
-- ledger is not observed by the source.
------------------------------------------------------------------------

record SelectedInferenceCrackSpread : Set where
  constructor selected-inference-crack-spread
  field
    model : String
    selfHostCentsPerMillionOutput : Nat
    hostedCentsPerMillionOutput : Nat
    buyerSpreadCentsPerMillionOutput : Nat
    buyerSpreadShareBpOfHostedPrice : Nat
    sameModelPaid : Bool
    sameServingConfigurationPaid : Bool
    buyerSubstitutionSpreadPaid : Bool
    providerMarginalCostPaid : Bool
    providerMarginPaid : Bool
    globalInferenceCrackSpreadPaid : Bool

open SelectedInferenceCrackSpread public

miniMaxM3SelectedCrackSpread : SelectedInferenceCrackSpread
miniMaxM3SelectedCrackSpread = selected-inference-crack-spread
  "MiniMax-M3"
  93
  120
  27
  2250
  true
  true
  true
  false
  false
  false

selectedHostingSpreadCentsIs27 :
  buyerSpreadCentsPerMillionOutput miniMaxM3SelectedCrackSpread ≡ 27
selectedHostingSpreadCentsIs27 = refl

selectedHostingSpreadDecomposesHostedPrice :
  hostedCentsPerMillionOutput miniMaxM3SelectedCrackSpread ≡
  selfHostCentsPerMillionOutput miniMaxM3SelectedCrackSpread +
  buyerSpreadCentsPerMillionOutput miniMaxM3SelectedCrackSpread
selectedHostingSpreadDecomposesHostedPrice = refl

selectedHostingSpreadShareBpIs2250 :
  buyerSpreadShareBpOfHostedPrice miniMaxM3SelectedCrackSpread ≡ 2250
selectedHostingSpreadShareBpIs2250 = refl

selectedSpreadCrossMultiplication :
  buyerSpreadCentsPerMillionOutput miniMaxM3SelectedCrackSpread * 10000 ≡
  hostedCentsPerMillionOutput miniMaxM3SelectedCrackSpread * 2250
selectedSpreadCrossMultiplication = refl

sameModelReceiptReused :
  SameModel.sameModelIdentity SameModel.miniMaxM3EngineeringComparison ≡ true
sameModelReceiptReused = SameModel.sameModelIdentityPaid

providerMarginStillOpen :
  providerMarginPaid miniMaxM3SelectedCrackSpread ≡ false
providerMarginStillOpen = refl

globalCrackSpreadStillOpen :
  globalInferenceCrackSpreadPaid miniMaxM3SelectedCrackSpread ≡ false
globalCrackSpreadStillOpen = refl

data BuyerSpreadImpliesProviderMarginPermission : Set where
data OneConfigurationImpliesGlobalCrackSpreadPermission : Set where

data EngineeringCostImpliesAuditedCostPermission : Set where

selectedCrackSpreadDoesNotCreateProviderMargin :
  BuyerSpreadImpliesProviderMarginPermission → ⊥
selectedCrackSpreadDoesNotCreateProviderMargin ()

oneConfigurationDoesNotCreateGlobalCrackSpread :
  OneConfigurationImpliesGlobalCrackSpreadPermission → ⊥
oneConfigurationDoesNotCreateGlobalCrackSpread ()

engineeringEstimateDoesNotCreateAuditedMarginalCost :
  EngineeringCostImpliesAuditedCostPermission → ⊥
engineeringEstimateDoesNotCreateAuditedMarginalCost ()

boundary : String
boundary =
  "For the selected MiniMax-M3 serving configuration, the source-paid engineering comparison gives a buyer-side hosted-vs-self-host spread of USD 0.27 per million output tokens, equal to 22.5 percent of the hosted price. This is the closest currently paid AI crack-spread analogue. It is configuration-sensitive and does not reveal provider marginal cost, provider gross margin, or a global inference spread."
