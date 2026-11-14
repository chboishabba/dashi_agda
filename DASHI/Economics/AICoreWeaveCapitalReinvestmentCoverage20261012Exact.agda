module DASHI.Economics.AICoreWeaveCapitalReinvestmentCoverage20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICompanyReturnRolloverTrajectory2026Exact as Company

------------------------------------------------------------------------
-- COREWEAVE H1-2026 CAPITAL REINVESTMENT COVERAGE
--
-- Same-period primary-filing coordinates already exist in the company owner:
-- operating cash flow = +USD 3.663B; capex = USD 14.117B; D&A = USD 2.540B.
-- This owner pays the exact internal-cash coverage observation without
-- relabelling growth capex as replacement capex or CFO-capex as sustainable FCF.
------------------------------------------------------------------------

record ReinvestmentCoverage : Set where
  constructor reinvestmentCoverage
  field
    company : String
    period : String
    operatingCashFlowMillionUSD : Nat
    capitalExpenditureMillionUSD : Nat
    depreciationAmortizationMillionUSD : Nat
    capexExceedsOperatingCashFlow : Bool
    cashFundingShortfallMillionUSD : Nat
    capexExceedsDepreciationAmortization : Bool
    samePeriodCoordinatesSourcePaid : Bool
    replacementCapexIdentified : Bool
    sustainableFreeCashFlowEstablished : Bool
    capitalRecoveryEstablished : Bool

open ReinvestmentCoverage public

coreWeaveH12026ReinvestmentCoverage : ReinvestmentCoverage
coreWeaveH12026ReinvestmentCoverage = reinvestmentCoverage
  "CoreWeave" "H1-2026"
  3663 14117 2540
  true 10454 true true false false false

------------------------------------------------------------------------
-- Same-object source receipts.
------------------------------------------------------------------------

coreWeaveOperatingCashFlowIs3663 :
  Company.magnitude (Company.operatingCashFlow Company.coreWeaveH12026) ≡ 3663
coreWeaveOperatingCashFlowIs3663 = refl

coreWeaveOperatingCashFlowIsPositive :
  Company.negative (Company.operatingCashFlow Company.coreWeaveH12026) ≡ false
coreWeaveOperatingCashFlowIsPositive = refl

coreWeaveCapexIs14117 :
  Company.capitalExpenditureMillionUSD Company.coreWeaveH12026 ≡ 14117
coreWeaveCapexIs14117 = refl

coreWeaveDepreciationAmortizationIs2540 :
  Company.depreciationAmortizationMillionUSD Company.coreWeaveH12026 ≡ 2540
coreWeaveDepreciationAmortizationIs2540 = refl

------------------------------------------------------------------------
-- Exact arithmetic receipt: 3,663 + 10,454 = 14,117.
------------------------------------------------------------------------

coreWeaveCashFundingShortfallArithmetic : 3663 + 10454 ≡ 14117
coreWeaveCashFundingShortfallArithmetic = refl

coreWeaveCashFundingShortfallIs10454 :
  cashFundingShortfallMillionUSD coreWeaveH12026ReinvestmentCoverage ≡ 10454
coreWeaveCashFundingShortfallIs10454 = refl

coreWeaveCapexExceedsCFO :
  capexExceedsOperatingCashFlow coreWeaveH12026ReinvestmentCoverage ≡ true
coreWeaveCapexExceedsCFO = refl

coreWeaveReplacementCapexStillUnidentified :
  replacementCapexIdentified coreWeaveH12026ReinvestmentCoverage ≡ false
coreWeaveReplacementCapexStillUnidentified = refl

coreWeaveSustainableFCFStillUnestablished :
  sustainableFreeCashFlowEstablished coreWeaveH12026ReinvestmentCoverage ≡ false
coreWeaveSustainableFCFStillUnestablished = refl

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data CapexShortfallImpliesDefaultPermission : Set where
data CapexExceedsDAImpliesReplacementCapexPermission : Set where
data CFOminusCapexImpliesSustainableFCFPermission : Set where

capexShortfallDoesNotAutoProveDefault : CapexShortfallImpliesDefaultPermission → ⊥
capexShortfallDoesNotAutoProveDefault ()

capexAboveDADoesNotIdentifyReplacementCapex :
  CapexExceedsDAImpliesReplacementCapexPermission → ⊥
capexAboveDADoesNotIdentifyReplacementCapex ()

samePeriodCFOCapexDoesNotAutoCreateSustainableFCF :
  CFOminusCapexImpliesSustainableFCFPermission → ⊥
samePeriodCFOCapexDoesNotAutoCreateSustainableFCF ()

boundary : String
boundary =
  "CoreWeave H1-2026 source-paid operating cash flow of USD 3.663B does not cover USD 14.117B reported capex; the exact same-period gap is USD 10.454B. This is an internal-funding/reinvestment-coverage observation, not an identification of replacement capex, sustainable free cash flow, default or terminal capital recovery."
