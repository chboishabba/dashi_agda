module DASHI.Economics.AIGalaxyHeliosLandlordEconomics20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primarySECInvestorPresentation : Source.SourceKind
primarySECInvestorPresentation = Source.namedSourceKind "primary SEC-filed investor presentation"

galaxyHeliosSource : Source.AttributedSource
galaxyHeliosSource = Source.mkNoDOISource
  "Galaxy Digital Inc."
  "Project Speed / Helios Phase II financing investor presentation"
  "SEC-filed investor presentation"
  "2026-07"
  "https://www.sec.gov/Archives/edgar/data/1859392/000185939226000068/launch8-kexhibit99172226.htm"
  primarySECInvestorPresentation
  "reports approximately USD 3.5B Phase-II financing, 260 MW critical IT load leased to CoreWeave, 15-year base lease, 13.7 percent starting monthly-recurring-charge gross yield on cost, approximately USD 10.4B minimum contracted lease payments, near-triple-net structure, and 90 percent-plus NOI margin target; expressly disclaims assurance that payments or timing will be realised"
  Source.publicAttribution

record LandlordProjectEconomics : Set where
  constructor landlord-project-economics
  field
    tenant : String
    financingMillionUSD : Nat
    criticalITMW : Nat
    baseLeaseYears : Nat
    startingGrossYieldBp : Nat
    minimumContractedLeasePaymentsMillionUSD : Nat
    leaseLevelMarginLowerBp : Nat
    nearTripleNet : Bool
    tenantPaysUtilitiesTaxesInsuranceMaintenance : Bool
    realisedLeaseCashPaid : Bool
    tenantROICPaid : Bool
    terminalDemandPaid : Bool

open LandlordProjectEconomics public

heliosPhaseIILandlordEconomics : LandlordProjectEconomics
heliosPhaseIILandlordEconomics = landlord-project-economics
  "CoreWeave" 3500 260 15 1370 10400 9000 true true false false false

startingGrossYieldBpIs1370 :
  startingGrossYieldBp heliosPhaseIILandlordEconomics ≡ 1370
startingGrossYieldBpIs1370 = refl

leaseLevelMarginLowerBpIs9000 :
  leaseLevelMarginLowerBp heliosPhaseIILandlordEconomics ≡ 9000
leaseLevelMarginLowerBpIs9000 = refl

data LandlordYieldImpliesTenantROICPermission : Set where
data ContractedYieldImpliesRealisedCashPermission : Set where
data LandlordEconomicsImpliesTerminalDemandPermission : Set where

landlordYieldDoesNotCreateCoreWeaveROIC : LandlordYieldImpliesTenantROICPermission → ⊥
landlordYieldDoesNotCreateCoreWeaveROIC ()

contractedYieldDoesNotCreateRealisedCash : ContractedYieldImpliesRealisedCashPermission → ⊥
contractedYieldDoesNotCreateRealisedCash ()

landlordEconomicsDoesNotCreateTerminalDemand : LandlordEconomicsImpliesTerminalDemandPermission → ⊥
landlordEconomicsDoesNotCreateTerminalDemand ()

boundary : String
boundary =
  "Galaxy's SEC-filed Helios Phase-II presentation pays a project-landlord economics coordinate: 13.7 percent starting gross yield-on-cost, 90 percent-plus NOI margin target, approximately USD 10.4B minimum contracted lease payments and a near-triple-net 15-year CoreWeave lease. This can coexist with weak tenant/provider capital returns. It is not CoreWeave ROIC, not realised lease cash, and not terminal-demand authority; the source itself disclaims assurance that payments/timing will occur."
