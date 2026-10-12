module DASHI.Economics.AICapitalBurdenRelocation20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIInfrastructureCommitmentTrajectory2026Exact as Commitment

------------------------------------------------------------------------
-- CAPITAL-BURDEN RELOCATION
--
-- Provider-side financing relief is not the same proposition as a reduction in
-- system-wide capital burden. A customer prepayment / customer-supplied asset
-- can move the financing location while preserving the amount of capital that
-- the ecosystem had to commit.
--
-- The generic/synthetic relocation below is exact. Oracle's disclosed USD 75B
-- customer-funded/customer-supplied hardware amount is used only as a scale
-- receipt. The source does not identify Oracle's counterfactual provider-side
-- financing requirement absent that structure, so no Oracle-specific
-- conservation equality is manufactured.
------------------------------------------------------------------------

record CapitalBurdenState : Set where
  constructor capital-burden-state
  field
    providerFundingBillionUSD : Nat
    customerFundingBillionUSD : Nat
    thirdPartyFundingBillionUSD : Nat

open CapitalBurdenState public

systemBurdenBillionUSD : CapitalBurdenState → Nat
systemBurdenBillionUSD state =
  providerFundingBillionUSD state +
  customerFundingBillionUSD state +
  thirdPartyFundingBillionUSD state

illustrativeBefore : CapitalBurdenState
illustrativeBefore = capital-burden-state 75 0 0

illustrativeAfter : CapitalBurdenState
illustrativeAfter = capital-burden-state 0 75 0

illustrativeBeforeSystemBurdenIs75 :
  systemBurdenBillionUSD illustrativeBefore ≡ 75
illustrativeBeforeSystemBurdenIs75 = refl

illustrativeAfterSystemBurdenIs75 :
  systemBurdenBillionUSD illustrativeAfter ≡ 75
illustrativeAfterSystemBurdenIs75 = refl

oracleCustomerFundedScaleIs75 :
  Commitment.customerPrepaidOrSuppliedHardwareBillionUSD
    Commitment.oracleCustomerFundedAIHardware ≡ 75
oracleCustomerFundedScaleIs75 = refl

record CapitalBurdenRelocationBoundary : Set where
  constructor capital-burden-relocation-boundary
  field
    providerFinancingNeedCanFall : Bool
    customerCapitalCommitmentCanRise : Bool
    systemBurdenCanRemainUnchanged : Bool
    sourceIdentifiesOracleCounterfactualProviderNeed : Bool
    sourceProvesOracleSystemBurdenUnchanged : Bool
    customerFundingEstablishesTerminalDemand : Bool

open CapitalBurdenRelocationBoundary public

currentRelocationBoundary : CapitalBurdenRelocationBoundary
currentRelocationBoundary = capital-burden-relocation-boundary
  true true true false false false

sourceDoesNotIdentifyOracleCounterfactualBurden :
  sourceIdentifiesOracleCounterfactualProviderNeed currentRelocationBoundary ≡ false
sourceDoesNotIdentifyOracleCounterfactualBurden = refl

customerFundingStillNotTerminalDemand :
  customerFundingEstablishesTerminalDemand currentRelocationBoundary ≡ false
customerFundingStillNotTerminalDemand = refl

data ProviderReliefImpliesSystemReliefPermission : Set where
data CustomerFundingErasesSystemBurdenPermission : Set where
data CustomerFundingImpliesTerminalDemandPermission : Set where
data OracleScaleImpliesCounterfactualConservationPermission : Set where

providerReliefDoesNotAutoCreateSystemRelief :
  ProviderReliefImpliesSystemReliefPermission → ⊥
providerReliefDoesNotAutoCreateSystemRelief ()

customerFundingDoesNotEraseSystemBurden :
  CustomerFundingErasesSystemBurdenPermission → ⊥
customerFundingDoesNotEraseSystemBurden ()

customerFundingDoesNotAutoCreateTerminalDemand :
  CustomerFundingImpliesTerminalDemandPermission → ⊥
customerFundingDoesNotAutoCreateTerminalDemand ()

oracleScaleDoesNotCreateCounterfactualConservation :
  OracleScaleImpliesCounterfactualConservationPermission → ⊥
oracleScaleDoesNotCreateCounterfactualConservation ()

boundary : String
boundary =
  "Customer-funded capacity can relocate financing from provider to customer without reducing the capital committed by the ecosystem. The exact 75/0 -> 0/75 example proves the accounting possibility; Oracle's USD 75B customer-prepaid/customer-supplied hardware disclosure supplies only the scale coordinate. It does not identify Oracle's counterfactual provider financing need, prove system burden unchanged, or establish independent terminal demand."
