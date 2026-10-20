module DASHI.Economics.AICoreWeaveSameObjectFinancingClock20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secFiledContractKind : Source.SourceKind
secFiledContractKind = Source.namedSourceKind "SEC-filed credit agreement / financing exhibit"

coreWeaveDDTL4Agreement : Source.AttributedSource
coreWeaveDDTL4Agreement = Source.mkNoDOISource
  "CoreWeave, Inc."
  "DDTL 4.0 Credit Agreement, Exhibit 10.1"
  "SEC-filed credit agreement"
  "2026-03-30"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000129/ex1011.htm"
  secFiledContractKind
  "defines GPU Depreciated Amount for financed Infrastructure on a straight-line GAAP basis assuming a six-year useful life; loans finance GPU servers and related infrastructure supporting a Master Service Agreement"
  Source.publicAttribution

coreWeaveDDTL55Agreement : Source.AttributedSource
coreWeaveDDTL55Agreement = Source.mkNoDOISource
  "CoreWeave, Inc."
  "DDTL 5.5 Credit Agreement, Exhibit 10.1"
  "SEC-filed credit agreement"
  "2026-08-07"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000357/ex101creditagreement.htm"
  secFiledContractKind
  "defines GPU Depreciated Amount on a six-year straight-line GAAP basis and includes a GPU Depreciation Amount Spreadsheet among the filed schedules"
  Source.publicAttribution

coreWeaveEarlierGPUAgreement : Source.AttributedSource
coreWeaveEarlierGPUAgreement = Source.mkNoDOISource
  "CoreWeave, Inc."
  "GPU-backed credit agreement exhibit filed with registration statement"
  "SEC-filed credit agreement"
  "2025-03-03"
  "https://www.sec.gov/Archives/edgar/data/1769628/000119312525044231/d899798dex108.htm"
  secFiledContractKind
  "defines redacted GPU classes with straight-line useful lives of five-and-one-half and six-and-one-half years for the contractual GPU Depreciated Amount"
  Source.publicAttribution

coreWeaveUsedGPUAgreement : Source.AttributedSource
coreWeaveUsedGPUAgreement = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Fifth Amendment DDTL credit agreement exhibit"
  "SEC-filed credit agreement"
  "2025-11-24"
  "https://www.sec.gov/Archives/edgar/data/1769628/000119312525227562/d910811dex101.htm"
  secFiledContractKind
  "defines Used GPU Server Depreciated Amount on a six-year straight-line basis from initial placed-in-service date through contribution date"
  Source.publicAttribution

record SameObjectFinancingClock : Set where
  constructor same-object-financing-clock
  field
    minimumObservedContractualGPUUsefulLifeMonths : Nat
    commonObservedContractualGPUUsefulLifeMonths : Nat
    maximumObservedContractualGPUUsefulLifeMonths : Nat
    companyTechnologyEquipmentAccountingLifeMonths : Nat
    sameObjectFinancingDepreciationObserved : Bool
    usedGPUContributionKeepsSixYearBasis : Bool
    generic36To48MonthHorizonSameObject : Bool
    old24To36MonthMismatchPromotable : Bool
    realisedEconomicLifePaid : Bool
    realisedRetirementTimingPaid : Bool

open SameObjectFinancingClock public

coreWeaveSameObjectFinancingClock : SameObjectFinancingClock
coreWeaveSameObjectFinancingClock = same-object-financing-clock
  66 72 78 72 true true false false false false

sameObjectSixYearDepreciationPaid :
  commonObservedContractualGPUUsefulLifeMonths coreWeaveSameObjectFinancingClock ≡ 72
sameObjectSixYearDepreciationPaid = refl

sameObjectFiveAndHalfToSixAndHalfYearRangePaid :
  (minimumObservedContractualGPUUsefulLifeMonths coreWeaveSameObjectFinancingClock ≡ 66) ×
  (maximumObservedContractualGPUUsefulLifeMonths coreWeaveSameObjectFinancingClock ≡ 78)
sameObjectFiveAndHalfToSixAndHalfYearRangePaid = refl , refl

usedGPUContributionRetainsSixYearBasis :
  usedGPUContributionKeepsSixYearBasis coreWeaveSameObjectFinancingClock ≡ true
usedGPUContributionRetainsSixYearBasis = refl

generic36To48MonthHorizonIsNotSameObject :
  generic36To48MonthHorizonSameObject coreWeaveSameObjectFinancingClock ≡ false
generic36To48MonthHorizonIsNotSameObject = refl

old24To36MonthMismatchNotPromotable :
  old24To36MonthMismatchPromotable coreWeaveSameObjectFinancingClock ≡ false
old24To36MonthMismatchNotPromotable = refl

data GenericLenderHorizonCreatesCoreWeaveLifePermission : Set where

genericMarketHorizonCannotCreateSameObjectLife :
  GenericLenderHorizonCreatesCoreWeaveLifePermission → ⊥
genericMarketHorizonCannotCreateSameObjectLife ()

boundary : String
boundary =
  "Primary CoreWeave financing documents materially correct the earlier generic-horizon interpretation. Same-object filed GPU-backed agreements publicly define contractual GPU/Infrastructure depreciation on six-year bases, with an earlier filed agreement using 5.5- and 6.5-year bases for redacted GPU classes; a later amendment explicitly retains a six-year basis for used GPU servers contributed into the financing structure. Therefore the separately reported generic 36-48 month lender/collateral horizon is not a CoreWeave same-object financing-life observation and cannot support a 24-36 month CoreWeave accounting-versus-financing mismatch. Contractual depreciation remains distinct from realised economic life, residual value, impairment and retirement timing."
