module DASHI.Economics.AICoreWeaveNumericalCapitalBounds20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- COREWEAVE NUMERICAL CAPITAL-RETURN BOUNDS
--
-- Declared convention:
--   * market equity = June-30-2026 historical market capitalization;
--   * net market invested capital = market equity + gross debt - unrestricted
--     cash - marketable securities;
--   * six-month operating loss is simply annualised x2 for a bounded operating-
--     return diagnostic, not claimed as a forecast;
--   * WACC weights use gross debt + market equity, as in the standard market-
--     value WACC convention;
--   * equity cost is bounded below by the June-30 10Y Treasury yield, i.e. a
--     non-negative equity-risk contribution assumption rather than a chosen beta;
--   * selected debt cost is bounded below by 8.5%, and the most favourable
--     federal tax shield admitted here is 21%, giving >= 6.715% after-tax debt
--     cost. Integer proof uses the still-more-conservative 6.71% floor.
--
-- This closes a numerical ROIC interval and beta-free WACC FLOOR, not a unique
-- WACC point.  It intentionally avoids manufacturing a short-history CRWV beta.
------------------------------------------------------------------------

primaryFilingKind : Source.SourceKind
primaryFilingKind = Source.namedSourceKind "primary SEC filing"

secondaryMarketHistoryKind : Source.SourceKind
secondaryMarketHistoryKind = Source.namedSourceKind "secondary historical market-cap series"

officialTreasuryKind : Source.SourceKind
officialTreasuryKind = Source.namedSourceKind "official US Treasury daily yield curve"

coreWeaveQ22026Filing : Source.AttributedSource
coreWeaveQ22026Filing = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Quarterly report for period ended June 30 2026"
  "SEC Form 10-Q"
  "2026-08-12"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm"
  primaryFilingKind
  "primary carrier for H1 operating loss, June-30 cash, marketable securities and total indebtedness"
  Source.publicAttribution

coreWeaveJune30MarketCapSource : Source.AttributedSource
coreWeaveJune30MarketCapSource = Source.mkNoDOISource
  "FinanceCharts"
  "CoreWeave market-cap history"
  "historical market-cap series"
  "2026-06-30"
  "https://www.financecharts.com/stocks/CRWV/summary/market-cap"
  secondaryMarketHistoryKind
  "secondary carrier reporting CRWV June-30-2026 close USD 99.54, approximately 551M shares and USD 54.306B market capitalization"
  Source.publicAttribution

june30TreasurySource : Source.AttributedSource
june30TreasurySource = Source.mkNoDOISource
  "U.S. Department of the Treasury"
  "Daily Treasury Par Yield Curve Rates"
  "official daily yield curve"
  "2026-06-30"
  "https://home.treasury.gov/resource-center/data-chart-center/interest-rates/TextView?field_tdr_date_value=202606&type=daily_treasury_yield_curve"
  officialTreasuryKind
  "official carrier for June-30-2026 10-year Treasury par yield of 4.44 percent"
  Source.publicAttribution

record MarketCapitalConvention : Set where
  constructor market-capital-convention
  field
    marketEquityMillionUSD : Nat
    grossDebtMillionUSD : Nat
    unrestrictedCashMillionUSD : Nat
    marketableSecuritiesMillionUSD : Nat
    netMarketInvestedCapitalMillionUSD : Nat
    h1OperatingLossMillionUSD : Nat
    annualizedOperatingLossMillionUSD : Nat
    grossCapitalForWACCWeightsMillionUSD : Nat
    riskFreeRateBp : Nat
    selectedDebtCostFloorBp : Nat
    conservativeAfterTaxDebtFloorBp : Nat
    federalTaxShieldCeilingBp : Nat
    betaChosen : Bool
    equityRiskPremiumChosen : Bool

open MarketCapitalConvention public

coreWeaveJune30Convention : MarketCapitalConvention
coreWeaveJune30Convention = market-capital-convention
  54306
  35551
  5524
  15
  84318
  193
  386
  89857
  444
  850
  671
  2100
  false
  false

marketEquityMillionUSDIs54306 :
  marketEquityMillionUSD coreWeaveJune30Convention ≡ 54306
marketEquityMillionUSDIs54306 = refl

netMarketInvestedCapitalMillionUSDIs84318 :
  netMarketInvestedCapitalMillionUSD coreWeaveJune30Convention ≡ 84318
netMarketInvestedCapitalMillionUSDIs84318 = refl

annualizedOperatingLossMillionUSDIs386 :
  annualizedOperatingLossMillionUSD coreWeaveJune30Convention ≡ 386
annualizedOperatingLossMillionUSDIs386 = refl

------------------------------------------------------------------------
-- ROIC magnitude interval:
--
-- 386 / 84,318 * 10,000 = 45.779... bp.
-- Avoid division in the kernel-facing receipt:
--   84,318 * 45 + 65,690 = 3,860,000
--   3,860,000 + 18,628 = 84,318 * 46
-- hence annualised operating return is strictly between -46bp and -45bp.
------------------------------------------------------------------------

roicAbove45BpWitness : 84318 * 45 + 65690 ≡ 386 * 10000
roicAbove45BpWitness = refl

roicBelow46BpWitness : 386 * 10000 + 18628 ≡ 84318 * 46
roicBelow46BpWitness = refl

annualizedMarketROICMagnitudeBetween45And46Bp : Bool
annualizedMarketROICMagnitudeBetween45And46Bp = true

------------------------------------------------------------------------
-- Beta-free WACC floor.
--
-- Use market-value weights on E=54,306 and D=35,551.  Require only
-- Ke >= Rf = 444bp and Kd_after_tax >= 671bp. Weighted floor numerator:
--   54,306*444 + 35,551*671 = 47,966,585.
-- Since
--   89,857*533 + 72,804 = 47,966,585,
-- WACC is > 533bp under these declared lower-bound assumptions.
------------------------------------------------------------------------

waccFloorWeightedNumerator :
  54306 * 444 + 35551 * 671 ≡ 47966585
waccFloorWeightedNumerator = refl

waccFloorAtLeast533BpWitness :
  89857 * 533 + 72804 ≡ 47966585
waccFloorAtLeast533BpWitness = refl

waccFloorAtLeast533Bp : Bool
waccFloorAtLeast533Bp = true

betaFreeWACCFloorPaid : Bool
betaFreeWACCFloorPaid = true

------------------------------------------------------------------------
-- Combining ROIC < -45bp with WACC > +533bp gives a conservative capital-
-- spread deficit greater than 578bp.  This is a lower bound on the magnitude,
-- not a unique WACC point.
------------------------------------------------------------------------

capitalSpreadDeficitAtLeast578Bp : Bool
capitalSpreadDeficitAtLeast578Bp = true

record NumericalCapitalBoundary : Set where
  constructor numerical-capital-boundary
  field
    declaredMarketCapitalROICIntervalPaid : Bool
    betaFreeWACCFloorPaidField : Bool
    minimumCapitalSpreadDeficitPaid : Bool
    waccPointPaid : Bool
    canonicalROICConventionEstablished : Bool
    insolvencyOrDefaultEstablished : Bool

open NumericalCapitalBoundary public

currentNumericalCapitalBoundary : NumericalCapitalBoundary
currentNumericalCapitalBoundary = numerical-capital-boundary
  true true true false false false

waccPointStillOpen : waccPointPaid currentNumericalCapitalBoundary ≡ false
waccPointStillOpen = refl

data NumericalBoundImpliesCanonicalROICPermission : Set where
data WACCFloorImpliesWACCPointPermission : Set where
data NegativeSpreadBoundImpliesDefaultPermission : Set where

marketConventionDoesNotBecomeCanonicalROIC :
  NumericalBoundImpliesCanonicalROICPermission → ⊥
marketConventionDoesNotBecomeCanonicalROIC ()

waccFloorDoesNotCreateWACCPoint : WACCFloorImpliesWACCPointPermission → ⊥
waccFloorDoesNotCreateWACCPoint ()

negativeSpreadBoundDoesNotCreateDefault : NegativeSpreadBoundImpliesDefaultPermission → ⊥
negativeSpreadBoundDoesNotCreateDefault ()

boundary : String
boundary =
  "Using a declared June-30-2026 market-capital convention, CoreWeave market equity is USD 54.306B, gross debt USD 35.551B, unrestricted cash USD 5.524B and marketable securities USD 0.015B, giving USD 84.318B net market invested capital. Simple x2 annualisation of the source-paid H1 operating loss gives an operating-return magnitude between 45 and 46 bp. With June-30 10Y Treasury 4.44%, selected debt-cost floor 8.5%, at most a 21% federal tax shield and no negative equity-risk contribution, market-value weighting gives a beta-free WACC floor above 533 bp. Hence the declared-convention ROIC-WACC deficit exceeds 578 bp. This is a numerical bound, not a unique WACC point, canonical ROIC convention, insolvency or default theorem."
