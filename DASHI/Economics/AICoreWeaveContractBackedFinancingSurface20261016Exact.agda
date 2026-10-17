module DASHI.Economics.AICoreWeaveContractBackedFinancingSurface20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secFinancingKind : Source.SourceKind
secFinancingKind = Source.namedSourceKind "SEC-filed financing agreement / issuer filing"

record FacilityObservation : Set where
  constructor facility-observation
  field
    facilityName : String
    commitmentMillionUSD : Nat
    sofrMarginBp : Nat
    customerContractBacked : Bool
    nonRecourse : Bool
    projectSpecific : Bool

open FacilityObservation public

ddtl3 : FacilityObservation
ddtl3 = facility-observation "DDTL 3.0" 2600 400 true false true

ddtl4 : FacilityObservation
ddtl4 = facility-observation "DDTL 4.0" 8500 225 true true true

ddtl5 : FacilityObservation
ddtl5 = facility-observation "DDTL 5.0" 3100 450 true false true

ddtl55 : FacilityObservation
ddtl55 = facility-observation "DDTL 5.5" 2600 550 true false true

ddtl3Source : Source.AttributedSource
ddtl3Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Current Report describing DDTL 3.0 Facility"
  "SEC filing"
  "2025-07-28"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962825000033/crwv-20250728.htm"
  secFinancingKind
  "USD2.6B delayed-draw facility primarily financing capex for a customer contract including GPU servers; SOFR loans at daily compounded SOFR plus 4.00 percent"
  Source.publicAttribution

ddtl4Source : Source.AttributedSource
ddtl4Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "CoreWeave closes landmark USD8.5B DDTL 4.0 financing"
  "SEC-filed issuer release"
  "2026-03-31"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000129/ex991.htm"
  secFinancingKind
  "USD8.5B non-recourse financing secured by HPC infrastructure and associated customer contract; floating tranche SOFR plus 2.25 percent and fixed tranche approximately 5.9 percent"
  Source.publicAttribution

ddtl5Source : Source.AttributedSource
ddtl5Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "DDTL 5.0 financing disclosure"
  "SEC filing"
  "2026-05-15"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000236/crwv-20260515.htm"
  secFinancingKind
  "USD3.1B delayed-draw facility primarily financing capex for customer contracts including GPU servers and infrastructure; SOFR loans at SOFR plus 4.50 percent"
  Source.publicAttribution

ddtl55Source : Source.AttributedSource
ddtl55Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "DDTL 5.5 financing disclosure"
  "SEC filing"
  "2026-08-07"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000357/crwv-20260807.htm"
  secFinancingKind
  "USD2.6B delayed-draw facility primarily financing capex for customer contracts including GPU servers and infrastructure; SOFR loans at SOFR plus 5.50 percent"
  Source.publicAttribution

ddtl3SOFRMarginBpIs400 : sofrMarginBp ddtl3 ≡ 400
ddtl3SOFRMarginBpIs400 = refl

ddtl4SOFRMarginBpIs225 : sofrMarginBp ddtl4 ≡ 225
ddtl4SOFRMarginBpIs225 = refl

ddtl5SOFRMarginBpIs450 : sofrMarginBp ddtl5 ≡ 450
ddtl5SOFRMarginBpIs450 = refl

ddtl55SOFRMarginBpIs550 : sofrMarginBp ddtl55 ≡ 550
ddtl55SOFRMarginBpIs550 = refl

financingRateIsProjectSpecific :
  (projectSpecific ddtl3 ≡ true) ×
  (projectSpecific ddtl4 ≡ true) ×
  (projectSpecific ddtl5 ≡ true) ×
  (projectSpecific ddtl55 ≡ true)
financingRateIsProjectSpecific = refl , refl , refl , refl

data OneCompanyWideRatePermission : Set where

oneCompanyWideRateNotPromotable : OneCompanyWideRatePermission → ⊥
oneCompanyWideRateNotPromotable ()

boundary : String
boundary =
  "CoreWeave's disclosed asset-level financing cost is a project/customer-contract/structure surface rather than one company-wide borrowing rate. Public filings show SOFR margins of 400bp for DDTL 3.0, 225bp for the non-recourse investment-grade DDTL 4.0 floating tranche, 450bp for DDTL 5.0, and 550bp for DDTL 5.5. These observations establish contract terms only; they do not identify a universal CoreWeave WACC, future refinancing cost, customer credit quality beyond disclosed structure, or realised project return."
