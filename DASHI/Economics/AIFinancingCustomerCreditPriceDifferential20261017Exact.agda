module DASHI.Economics.AIFinancingCustomerCreditPriceDifferential20261017Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primaryFiledCompanyDisclosure : Source.SourceKind
primaryFiledCompanyDisclosure = Source.namedSourceKind "company results exhibit filed with SEC"

irenFY26ResultsSource : Source.AttributedSource
irenFY26ResultsSource = Source.mkNoDOISource
  "IREN Limited"
  "IREN Reports FY26 Results"
  "SEC-filed company exhibit"
  "2026-08-27"
  "https://www.sec.gov/Archives/edgar/data/1878848/000187884826000051/irenreportsfy26results.htm"
  primaryFiledCompanyDisclosure
  "IREN reported 3.6 billion dollars of investment-grade GPU financing for the Microsoft contract at 6.0 percent and 2.8 billion dollars of new GPU financings for non-investment-grade customer deployments, including a 2.4 billion dollar financing at 9.0 percent fixed for Mackenzie. The company said the Microsoft facility together with prepayments funded 96 percent of associated GPU capex; the Mackenzie financing funded 90 percent before customer prepayments."
  Source.publicAttribution

record FinancingPriceDifferential : Set where
  constructor financing-price-differential
  field
    company : String
    investmentGradeSelectedRateBasisPoints : Nat
    nonInvestmentGradeSelectedRateBasisPoints : Nat
    selectedRateDifferenceBasisPoints : Nat
    sameCompanyObservation : Bool
    sameInstrument : Bool
    sameCollateral : Bool
    sameMaturity : Bool
    sameProject : Bool
    pureCustomerCreditCausalEffectPaid : Bool
    positiveProjectReturnPaid : Bool

open FinancingPriceDifferential public

irenSelectedFinancingDifferential : FinancingPriceDifferential
irenSelectedFinancingDifferential = financing-price-differential
  "IREN" 600 900 300 true false false false false false false

selectedDifferentialIs300bp : selectedRateDifferenceBasisPoints irenSelectedFinancingDifferential ≡ 300
selectedDifferentialIs300bp = refl

sameCompanyObservationPaid : sameCompanyObservation irenSelectedFinancingDifferential ≡ true
sameCompanyObservationPaid = refl

causalEffectStillOpen : pureCustomerCreditCausalEffectPaid irenSelectedFinancingDifferential ≡ false
causalEffectStillOpen = refl

data RateDifferenceEqualsCustomerCreditEffectPermission : Set where
data LowerRateImpliesPositiveReturnPermission : Set where

rateDifferenceDoesNotIdentifyCustomerCreditEffect : RateDifferenceEqualsCustomerCreditEffectPermission → ⊥
rateDifferenceDoesNotIdentifyCustomerCreditEffect ()

lowerRateDoesNotCreatePositiveReturn : LowerRateImpliesPositiveReturnPermission → ⊥
lowerRateDoesNotCreatePositiveReturn ()

boundary : String
boundary =
  "IREN's SEC-filed FY26 results provide a selected same-company financing-price observation: 6.0 percent on an investment-grade Microsoft GPU financing versus 9.0 percent on a selected non-investment-grade Mackenzie financing, a DASHI-derived 300 basis-point arithmetic difference. The filing owns the disclosed rates and financing descriptions; DASHI owns only the subtraction and typed comparison. Because the facilities are not established as matched on instrument, collateral, maturity or project, the 300 basis points are not promoted into a pure customer-credit causal effect. Lower financing cost also does not establish positive project return or terminal demand."
