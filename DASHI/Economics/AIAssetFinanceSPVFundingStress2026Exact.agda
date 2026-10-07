module DASHI.Economics.AIAssetFinanceSPVFundingStress2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AIEnergyInfrastructureFundingStress2026Exact as Funding
import DASHI.Economics.ReflexiveFlowValidationExact as Flow

------------------------------------------------------------------------
-- AI ASSET-FINANCE / SPV / LEASEBACK STRESS, OCTOBER 2026
--
-- Asset transfer, SPV debt and leaseback can change balance-sheet placement,
-- funding source and loss allocation without changing the underlying physical
-- compute requirement.  This owner records topology; it does not infer
-- accounting impropriety, hidden debt, insolvency or bubble status.
------------------------------------------------------------------------

reutersAmazonChipSPV2026 : Source.AttributedSource
reutersAmazonChipSPV2026 = Source.mkNoDOISource
  "Reuters"
  "Amazon seeks to offload $8 billion of Nvidia chips to investors, FT reports"
  "Reuters"
  "2026-10-02"
  "https://www.reuters.com/business/retail-consumer/amazon-seeks-offload-8-billion-nvidia-chips-investors-ft-reports-2026-10-02/"
  Source.newsSource
  "secondary carrier for the reported exploration of transferring about USD 8 billion of installed Nvidia chips into an investor-funded SPV and leasing them back"
  Source.publicAttribution

reutersSoftBankHighYield2026 : Source.AttributedSource
reutersSoftBankHighYield2026 = Source.mkNoDOISource
  "Reuters"
  "AI borrowers face tough sell in risky corners of US credit market"
  "Reuters"
  "2026-09-30"
  "https://www.reuters.com/legal/transactional/ai-borrowers-face-tough-sell-risky-corners-us-credit-market-2026-09-30/"
  Source.newsSource
  "secondary carrier for SoftBank-reported yields of 8.625 percent, 9.25 percent and 9.75 percent across 3.5-, 5.5- and 7.5-year debt; not a universal AI hurdle-rate rule"
  Source.publicAttribution

record AssetFinanceTopology : Set where
  constructor assetFinanceTopology
  field
    assetTransferredToSPV : Bool
    externalDebtFinancesSPV : Bool
    originalOperatorLeasesAssetBack : Bool
    outsideEquityPossible : Bool
    physicalComputeStillRequired : Bool
    balanceSheetPlacementChanges : Bool

open AssetFinanceTopology public

amazonReportedSPVTopology : AssetFinanceTopology
amazonReportedSPVTopology = assetFinanceTopology
  true true true true true true

record FundingCurveObservation : Set where
  constructor fundingCurveObservation
  field
    issuer : String
    rating : String
    shortYieldReading : String
    mediumYieldReading : String
    longYieldReading : String
    source : Source.AttributedSource
    establishesUniversalHurdleRate : Bool

open FundingCurveObservation public

softBankSeptember2026Curve : FundingCurveObservation
softBankSeptember2026Curve = fundingCurveObservation
  "SoftBank Group"
  "BB+ as reported by Reuters"
  "8.625 percent / 3.5-year"
  "9.25 percent / 5.5-year"
  "9.75 percent / 7.5-year"
  reutersSoftBankHighYield2026
  false

record AssetFinanceStressCoordinates : Set where
  constructor assetFinanceStressCoordinates
  field
    leasebackIntensity : Trit
    externalDebtDependence : Trit
    residualValueSensitivity : Trit
    refinancingSensitivity : Trit
    accountingPlacementComplexity : Trit
    terminalPayerValidation : Trit

open AssetFinanceStressCoordinates public

candidateOctober2026AssetFinanceStress : AssetFinanceStressCoordinates
candidateOctober2026AssetFinanceStress =
  assetFinanceStressCoordinates pos pos pos pos pos neg

data SPVImpliesHiddenDebtPermission : Set where
data LeasebackImpliesEconomicDeleveragingPermission : Set where
data HighYieldImpliesInsolvencyPermission : Set where
data AssetTransferImpliesTerminalDemandPermission : Set where

spvDoesNotAutoProveHiddenDebt : SPVImpliesHiddenDebtPermission → ⊥
spvDoesNotAutoProveHiddenDebt ()

leasebackDoesNotAutoProveEconomicDeleveraging :
  LeasebackImpliesEconomicDeleveragingPermission → ⊥
leasebackDoesNotAutoProveEconomicDeleveraging ()

highYieldDoesNotAutoProveInsolvency : HighYieldImpliesInsolvencyPermission → ⊥
highYieldDoesNotAutoProveInsolvency ()

assetTransferDoesNotAutoManufactureTerminalDemand :
  AssetTransferImpliesTerminalDemandPermission → ⊥
assetTransferDoesNotAutoManufactureTerminalDemand ()

fundingClockStillOpen : Funding.FundingClock
fundingClockStillOpen = Funding.candidateBurryStyleFundingClock

markedGainStillDoesNotCloseExternalCash :
  Flow.MarkedGainImpliesExternalCashPermission → ⊥
markedGainStillDoesNotCloseExternalCash =
  Flow.markedGainDoesNotAutoPromoteToExternalCash
