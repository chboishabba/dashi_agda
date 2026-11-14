module DASHI.Economics.AIIRENProjectPaybackExpectation20261017Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primaryFiledCompanyForecast : Source.SourceKind
primaryFiledCompanyForecast = Source.namedSourceKind "company forecast/estimate filed with SEC"

irenFY26ResultsSource : Source.AttributedSource
irenFY26ResultsSource = Source.mkNoDOISource
  "IREN Limited"
  "IREN Reports FY26 Results"
  "SEC-filed company exhibit"
  "2026-08-27"
  "https://www.sec.gov/Archives/edgar/data/1878848/000187884826000051/irenreportsfy26results.htm"
  primaryFiledCompanyForecast
  "IREN stated that recent three-year AI Cloud contracts exceeded 20 million dollars revenue per MW and represented approximately two-year payback under the company's framing; recent customer prepayments represented 45 to 55 percent of GPU capex."
  Source.publicAttribution

record ProjectPaybackExpectation : Set where
  constructor project-payback-expectation
  field
    subject : String
    contractTermYears : Nat
    revenuePerMWFloorUSDm : Nat
    companyEstimatedPaybackYears : Nat
    customerPrepaymentLowerPercent : Nat
    customerPrepaymentUpperPercent : Nat
    companyPaybackExpectationPaid : Bool
    realisedPaybackPaid : Bool
    realisedProjectIRRPaid : Bool
    sameProjectCashFlowPaid : Bool

open ProjectPaybackExpectation public

irenSelectedProjectExpectation : ProjectPaybackExpectation
irenSelectedProjectExpectation = project-payback-expectation
  "IREN recent selected AI Cloud contracts" 3 20 2 45 55 true false false false

forecastPaid : companyPaybackExpectationPaid irenSelectedProjectExpectation ≡ true
forecastPaid = refl

realisedPaybackStillOpen : realisedPaybackPaid irenSelectedProjectExpectation ≡ false
realisedPaybackStillOpen = refl

data ForecastEqualsRealisedReturnPermission : Set where
data RevenuePerMWEqualsFreeCashFlowPermission : Set where

forecastDoesNotCreateRealisedReturn : ForecastEqualsRealisedReturnPermission → ⊥
forecastDoesNotCreateRealisedReturn ()

revenuePerMWDoesNotCreateFCF : RevenuePerMWEqualsFreeCashFlowPermission → ⊥
revenuePerMWDoesNotCreateFCF ()

boundary : String
boundary =
  "IREN's SEC-filed FY26 results supply a company-owned ex-ante project-economics claim: selected recent three-year contracts above 20 million dollars revenue per MW were described as representing roughly two-year payback, alongside 45-55 percent customer prepayments of GPU capex. This is a forecast/management estimate, not an audited realised project return. DASHI records the forecast as a falsifiable future socket only; revenue per MW is not free cash flow, a stated payback is not realised IRR, and customer prepayment does not establish terminal demand or capital recovery."
