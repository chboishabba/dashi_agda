module DASHI.Economics.AIGalaxyHeliosLandlordEconomics20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primarySECInvestorPresentation : Source.SourceKind
primarySECInvestorPresentation = Source.namedSourceKind "primary SEC-filed investor presentation"

primarySECQuarterlyFiling : Source.SourceKind
primarySECQuarterlyFiling = Source.namedSourceKind "primary SEC quarterly filing"

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

galaxyQ22026Source : Source.AttributedSource
galaxyQ22026Source = Source.mkNoDOISource
  "Galaxy Digital Inc."
  "Quarterly report for period ended June 30 2026"
  "SEC Form 10-Q"
  "2026-08"
  "https://www.sec.gov/Archives/edgar/data/1859392/000185939226000091/glxy-20260630.htm"
  primarySECQuarterlyFiling
  "reports USD 18.9M data-center lease revenue attributable to commencement of the CoreWeave Phase-I lease and USD 5.8M data-center operator revenue attributable to pass-through operating costs related to the CoreWeave lease"
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
    phaseILeaseRevenueHundredThousandUSD : Nat
    phaseIOperatorRevenueHundredThousandUSD : Nat
    realisedLeaseRevenuePaid : Bool
    realisedLeaseCashCollectionPaid : Bool
    tenantROICPaid : Bool
    terminalDemandPaid : Bool

open LandlordProjectEconomics public

heliosPhaseIILandlordEconomics : LandlordProjectEconomics
heliosPhaseIILandlordEconomics = landlord-project-economics
  "CoreWeave" 3500 260 15 1370 10400 9000 true true 189 58 true false false false

startingGrossYieldBpIs1370 :
  startingGrossYieldBp heliosPhaseIILandlordEconomics ≡ 1370
startingGrossYieldBpIs1370 = refl

leaseLevelMarginLowerBpIs9000 :
  leaseLevelMarginLowerBp heliosPhaseIILandlordEconomics ≡ 9000
leaseLevelMarginLowerBpIs9000 = refl

phaseILeaseRevenueHundredThousandUSDIs189 :
  phaseILeaseRevenueHundredThousandUSD heliosPhaseIILandlordEconomics ≡ 189
phaseILeaseRevenueHundredThousandUSDIs189 = refl

phaseIOperatorRevenueHundredThousandUSDIs58 :
  phaseIOperatorRevenueHundredThousandUSD heliosPhaseIILandlordEconomics ≡ 58
phaseIOperatorRevenueHundredThousandUSDIs58 = refl

realisedLeaseRevenueObserved :
  realisedLeaseRevenuePaid heliosPhaseIILandlordEconomics ≡ true
realisedLeaseRevenueObserved = refl

cashCollectionStillOpen :
  realisedLeaseCashCollectionPaid heliosPhaseIILandlordEconomics ≡ false
cashCollectionStillOpen = refl

data LandlordYieldImpliesTenantROICPermission : Set where
data ContractedYieldImpliesRealisedCashPermission : Set where
data RecognisedRevenueImpliesCashCollectionPermission : Set where
data LandlordEconomicsImpliesTerminalDemandPermission : Set where

landlordYieldDoesNotCreateCoreWeaveROIC : LandlordYieldImpliesTenantROICPermission → ⊥
landlordYieldDoesNotCreateCoreWeaveROIC ()

contractedYieldDoesNotCreateRealisedCash : ContractedYieldImpliesRealisedCashPermission → ⊥
contractedYieldDoesNotCreateRealisedCash ()

recognisedRevenueDoesNotCreateCashCollection : RecognisedRevenueImpliesCashCollectionPermission → ⊥
recognisedRevenueDoesNotCreateCashCollection ()

landlordEconomicsDoesNotCreateTerminalDemand : LandlordEconomicsImpliesTerminalDemandPermission → ⊥
landlordEconomicsDoesNotCreateTerminalDemand ()

boundary : String
boundary =
  "Galaxy's SEC-filed Helios material now pays both contracted/project economics and an early realised revenue coordinate. Phase II targets a 13.7 percent starting gross yield-on-cost and 90 percent-plus NOI margin under a near-triple-net 15-year CoreWeave lease. Separately, Galaxy's Q2-2026 10-Q recognises USD 18.9M of Phase-I lease revenue plus USD 5.8M operator revenue tied to pass-through lease operating costs. Revenue recognition does not itself prove cash collection, Phase-II target realisation, CoreWeave ROIC, or terminal demand."
