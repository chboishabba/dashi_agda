module DASHI.Economics.AICompanyReturnRolloverTrajectory2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AIPartialCoordinateBounds2026Exact as Bounds

------------------------------------------------------------------------
-- REALISED RETURN / PAYER / ROLLOVER TRAJECTORIES
--
-- Company accounting trajectories are source evidence, not realised ROIC.
-- Customer concentration is distinct from independent-terminal-payer status.
-- Contractual debt schedules are distinct from insolvency/default findings.
------------------------------------------------------------------------

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC filing"

coreWeaveQ22026Source : Source.AttributedSource
coreWeaveQ22026Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Quarterly Report for quarter ended June 30, 2026"
  "SEC Form 10-Q"
  "2026-08"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm"
  secFilingKind
  "primary carrier for H1 2026 revenue, operating loss, interest expense, operating cash flow, property/equipment purchases, depreciation and principal maturity table"
  Source.publicAttribution

coreWeaveSeptember2026Source : Source.AttributedSource
coreWeaveSeptember2026Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "September 2026 filing"
  "SEC filing"
  "2026-09-18"
  "https://www.sec.gov/Archives/edgar/data/2110365/000119312526395475/ck0002110365-20260918.htm"
  secFilingKind
  "primary carrier for largest-customer revenue concentration and Microsoft/Anthropic committed-payment disclosures"
  Source.publicAttribution

cerebrasQ22026Source : Source.AttributedSource
cerebrasQ22026Source = Source.mkNoDOISource
  "Cerebras Systems Inc."
  "Quarterly Report for quarter ended June 30, 2026"
  "SEC Form 10-Q"
  "2026-08-12"
  "https://www.sec.gov/Archives/edgar/data/2021728/000162828026056357/cbrs-20260630.htm"
  secFilingKind
  "primary carrier for H1 revenue/cash flow/capex/customer concentration, OpenAI revenue, remaining performance obligations and working-capital-loan structure"
  Source.publicAttribution

record SignedMillion : Set where
  constructor signedMillion
  field
    magnitude : Nat
    negative : Bool

record RealisedOperatingPeriod : Set where
  constructor realisedOperatingPeriod
  field
    company : String
    period : String
    revenueMillionUSD : Nat
    operatingIncome : SignedMillion
    interestExpenseMillionUSD : Nat
    operatingCashFlow : SignedMillion
    capitalExpenditureMillionUSD : Nat
    depreciationAmortizationMillionUSD : Nat
    source : Source.AttributedSource
    realisedROICKnown : Bool
    waccKnown : Bool

coreWeaveH12025 : RealisedOperatingPeriod
coreWeaveH12025 = realisedOperatingPeriod
  "CoreWeave" "H1-2025" 2194
  (signedMillion 8 true)
  531
  (signedMillion 190 true)
  3860
  1003
  coreWeaveQ22026Source
  false false

coreWeaveH12026 : RealisedOperatingPeriod
coreWeaveH12026 = realisedOperatingPeriod
  "CoreWeave" "H1-2026" 4653
  (signedMillion 193 true)
  1176
  (signedMillion 3663 false)
  14117
  2540
  coreWeaveQ22026Source
  false false

cerebrasH12025 : RealisedOperatingPeriod
cerebrasH12025 = realisedOperatingPeriod
  "Cerebras" "H1-2025" 203
  (signedMillion 86 true)
  0
  (signedMillion 124 true)
  185
  9
  cerebrasQ22026Source
  false false

cerebrasH12026 : RealisedOperatingPeriod
cerebrasH12026 = realisedOperatingPeriod
  "Cerebras" "H1-2026" 374
  (signedMillion 492 true)
  0
  (signedMillion 47 true)
  549
  43
  cerebrasQ22026Source
  false false

------------------------------------------------------------------------
-- Customer-concentration interval trajectories (HHI scaled by 10,000).
------------------------------------------------------------------------

record ConcentrationIntervalTrajectory : Set where
  constructor concentrationIntervalTrajectory
  field
    company : String
    earlierPeriod : String
    earlierLowerHHIbp : Nat
    earlierUpperHHIbp : Nat
    laterPeriod : String
    laterLowerHHIbp : Nat
    laterUpperHHIbp : Nat
    realisedConcentrationLowerFell : Bool
    realisedConcentrationUpperFell : Bool
    terminalPayerIdentityEstablished : Bool

coreWeaveConcentrationTrajectory : ConcentrationIntervalTrajectory
coreWeaveConcentrationTrajectory = concentrationIntervalTrajectory
  "CoreWeave" "2025" 5329 6058 "H1-2026" 2704 5008
  true true false

cerebrasConcentrationTrajectory : ConcentrationIntervalTrajectory
cerebrasConcentrationTrajectory = concentrationIntervalTrajectory
  "Cerebras" "H1-2025" 3890 4034 "H1-2026" 3001 3122
  true true false

------------------------------------------------------------------------
-- Contractual rollover / amortisation evidence.
------------------------------------------------------------------------

record PrincipalMaturitySchedule : Set where
  constructor principalMaturitySchedule
  field
    company : String
    remaining2026MillionUSD : Nat
    y2027MillionUSD : Nat
    y2028MillionUSD : Nat
    y2029MillionUSD : Nat
    y2030MillionUSD : Nat
    thereafterMillionUSD : Nat
    totalMillionUSD : Nat
    dueThrough2027ShareBp : Nat
    dueThrough2028ShareBp : Nat
    source : Source.AttributedSource

coreWeavePrincipalMaturities : PrincipalMaturitySchedule
coreWeavePrincipalMaturities = principalMaturitySchedule
  "CoreWeave" 4413 6184 4416 2421 3221 14896 35551
  2981 4223 coreWeaveQ22026Source

record CustomerFinancedAmortisation : Set where
  constructor customerFinancedAmortisation
  field
    company : String
    customerFinancier : String
    originalPrincipalMillionUSD : Nat
    outstandingPrincipalMillionUSD : Nat
    currentPortionMillionUSD : Nat
    longTermPortionMillionUSD : Nat
    statedInterestRateBp : Nat
    legalMaturity : String
    serviceCreditsCanRepayPrincipal : Bool
    terminationCanAccelerateRepayment : Bool
    source : Source.AttributedSource

cerebrasOpenAIWorkingCapitalLoan : CustomerFinancedAmortisation
cerebrasOpenAIWorkingCapitalLoan = customerFinancedAmortisation
  "Cerebras" "OpenAI" 1005 918 736 182 600 "2032-12-31"
  true true cerebrasQ22026Source

record ForwardRevenueConcentration : Set where
  constructor forwardRevenueConcentration
  field
    company : String
    remainingPerformanceObligationMillionUSD : Nat
    first24MonthShareBp : Nat
    months25To48ShareBp : Nat
    laterShareBp : Nat
    namedCustomerIsSignificantComponent : Bool
    namedCustomer : String
    source : Source.AttributedSource

cerebrasForwardOpenAIConcentration : ForwardRevenueConcentration
cerebrasForwardOpenAIConcentration = forwardRevenueConcentration
  "Cerebras" 25400 2200 4300 3500 true "OpenAI" cerebrasQ22026Source

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

data AccountingGrowthImpliesROICPermission : Set where
data PositiveOperatingCashFlowImpliesCapitalRecoveryPermission : Set where
data CustomerConcentrationDeclineImpliesTerminalIndependencePermission : Set where
data DebtMaturityScheduleImpliesDefaultPermission : Set where
data CustomerFinancedLoanImpliesCircularRevenuePermission : Set where

accountingGrowthDoesNotAutoCreateROIC :
  AccountingGrowthImpliesROICPermission → ⊥
accountingGrowthDoesNotAutoCreateROIC ()

positiveOperatingCashFlowDoesNotAutoCreateCapitalRecovery :
  PositiveOperatingCashFlowImpliesCapitalRecoveryPermission → ⊥
positiveOperatingCashFlowDoesNotAutoCreateCapitalRecovery ()

concentrationDeclineDoesNotAutoCreateTerminalIndependence :
  CustomerConcentrationDeclineImpliesTerminalIndependencePermission → ⊥
concentrationDeclineDoesNotAutoCreateTerminalIndependence ()

debtScheduleDoesNotAutoProveDefault : DebtMaturityScheduleImpliesDefaultPermission → ⊥
debtScheduleDoesNotAutoProveDefault ()

customerFinancedLoanDoesNotAutoProveCircularRevenue :
  CustomerFinancedLoanImpliesCircularRevenuePermission → ⊥
customerFinancedLoanDoesNotAutoProveCircularRevenue ()

returnAuthorityStillOpen : realisedROICKnown coreWeaveH12026 ≡ false
returnAuthorityStillOpen = refl

cerebrasReturnAuthorityStillOpen : realisedROICKnown cerebrasH12026 ≡ false
cerebrasReturnAuthorityStillOpen = refl
