module DASHI.Economics.AIFinancingCohortCompanyOutcomeCoordinates20261017Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primaryFiledFinancialResult : Source.SourceKind
primaryFiledFinancialResult = Source.namedSourceKind "company financial result filed with SEC"

nebiusQ22026Filing : Source.AttributedSource
nebiusQ22026Filing = Source.mkNoDOISource
  "Nebius Group N.V."
  "Q2 2026 financial results and shareholder letter"
  "SEC-filed 6-K exhibits"
  "2026-08-12"
  "https://www.sec.gov/Archives/edgar/data/1513845/000110465926094844/nbis-20260812xex99d1.htm"
  primaryFiledFinancialResult
  "For the six months ended 2026-06-30 Nebius reported 4,504.1 million dollars net operating cash inflow and 8,130.3 million dollars purchases of property/equipment/intangibles; the filing says operating cash was driven primarily by customer advance payments that increased deferred revenue by 4,395.0 million dollars. The shareholder letter reports a 303.9 million dollar H1 operating loss."
  Source.publicAttribution

irenFY2026Filing : Source.AttributedSource
irenFY2026Filing = Source.mkNoDOISource
  "IREN Limited"
  "Annual Report for year ended June 30 2026"
  "SEC-filed annual report"
  "2026-06-30"
  "https://www.sec.gov/Archives/edgar/data/1878848/000187884826000052/iren-20260630.htm"
  primaryFiledFinancialResult
  "For FY2026 IREN reported 2,100.418 million dollars operating cash inflow, 4,722.984 million dollars investing cash outflow, 9,680.050 million dollars financing cash inflow, 1,046.714 million dollars operating loss and 128.795 million dollars AI Cloud Services revenue. The filing attributes much of investing cash to AI hardware and data-centre buildout while the company remains in transition from Bitcoin mining."
  Source.publicAttribution

record CompanyOutcomeCoordinate : Set where
  constructor company-outcome-coordinate
  field
    subject : String
    horizon : String
    operatingCashFlowUSDm : Nat
    investmentOrCapexOutflowUSDm : Nat
    operatingLossUSDm : Nat
    operatingLossObserved : Bool
    customerAdvanceMaterialToOCF : Bool
    financingCashInflowUSDm : Nat
    aiRevenueUSDm : Nat
    projectSpecificReturnPaid : Bool
    terminalDemandPaid : Bool

open CompanyOutcomeCoordinate public

nebiusH12026 : CompanyOutcomeCoordinate
nebiusH12026 = company-outcome-coordinate
  "Nebius" "H1 2026" 4504 8130 304 true true 9160 0 false false

irenFY2026 : CompanyOutcomeCoordinate
irenFY2026 = company-outcome-coordinate
  "IREN" "FY2026" 2100 4723 1047 true false 9680 129 false false

nebiusAdvanceDrivenCashPaid : customerAdvanceMaterialToOCF nebiusH12026 ≡ true
nebiusAdvanceDrivenCashPaid = refl

nebiusOperatingLossPaid : operatingLossObserved nebiusH12026 ≡ true
nebiusOperatingLossPaid = refl

irenOperatingLossPaid : operatingLossObserved irenFY2026 ≡ true
irenOperatingLossPaid = refl

record CompanyOutcomeBoundary : Set where
  constructor company-outcome-boundary
  field
    positiveOCFSelectsProjectReturn : Bool
    positiveOCFSelectsTerminalDemand : Bool
    companyOutcomeSelectsProjectOutcome : Bool
    customerAdvanceEqualsIndependentTerminalCash : Bool
    financingCashEqualsOperatingReturn : Bool

open CompanyOutcomeBoundary public

currentCompanyOutcomeBoundary : CompanyOutcomeBoundary
currentCompanyOutcomeBoundary = company-outcome-boundary false false false false false

positiveOCFDoesNotSelectProjectReturn : positiveOCFSelectsProjectReturn currentCompanyOutcomeBoundary ≡ false
positiveOCFDoesNotSelectProjectReturn = refl

positiveOCFDoesNotSelectTerminalDemand : positiveOCFSelectsTerminalDemand currentCompanyOutcomeBoundary ≡ false
positiveOCFDoesNotSelectTerminalDemand = refl

companyOutcomeDoesNotSelectProjectOutcome : companyOutcomeSelectsProjectOutcome currentCompanyOutcomeBoundary ≡ false
companyOutcomeDoesNotSelectProjectOutcome = refl

data OCFImpliesProjectReturnPermission : Set where
data CustomerAdvanceImpliesTerminalIndependencePermission : Set where
data FinancingCashImpliesReturnPermission : Set where

ocfDoesNotCreateProjectReturn : OCFImpliesProjectReturnPermission → ⊥
ocfDoesNotCreateProjectReturn ()

customerAdvanceDoesNotCreateTerminalIndependence : CustomerAdvanceImpliesTerminalIndependencePermission → ⊥
customerAdvanceDoesNotCreateTerminalIndependence ()

financingCashDoesNotCreateReturn : FinancingCashImpliesReturnPermission → ⊥
financingCashDoesNotCreateReturn ()

boundary : String
boundary =
  "Primary SEC-filed company results provide the first consumer-side outcome coordinates for the matched financing cohort. Nebius H1 2026 combined positive operating cash flow with a substantial operating loss and even larger property/equipment/intangible purchases; its filing explicitly says customer advances were the principal driver of operating cash. IREN FY2026 likewise combined positive operating cash flow with a substantial operating loss, larger investing outflows and very large financing inflows. These are company-level accounting/cash observations, not matched project returns. Positive OCF can be materially advance/prepayment-driven during buildout and therefore does not by itself establish terminal independent demand, positive project economics or capital recovery. Rounded Nat coordinates are DASHI comparison fixtures derived from the source figures; exact decimal filing values remain source-owned."
