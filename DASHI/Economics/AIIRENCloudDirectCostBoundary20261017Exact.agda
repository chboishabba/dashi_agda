module DASHI.Economics.AIIRENCloudDirectCostBoundary20261017Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primaryFiledSegmentAccounting : Source.SourceKind
primaryFiledSegmentAccounting = Source.namedSourceKind "audited segment accounting in SEC-filed annual report"

irenAnnualReport : Source.AttributedSource
irenAnnualReport = Source.mkNoDOISource
  "IREN Limited"
  "Annual Report for year ended June 30 2026"
  "SEC-filed annual report"
  "2026-06-30"
  "https://www.sec.gov/Archives/edgar/data/1878848/000187884826000052/iren-20260630.htm"
  primaryFiledSegmentAccounting
  "IREN reported FY2026 AI Cloud Services revenue of 128.795 million dollars and AI Cloud cost of revenue of 16.932 million dollars, with the cost-of-revenue line explicitly excluding depreciation and amortization shown separately."
  Source.publicAttribution

record CloudDirectCostCoordinate : Set where
  constructor cloud-direct-cost-coordinate
  field
    provider : String
    horizon : String
    revenueUSDthousands : Nat
    directCostUSDthousands : Nat
    directCostRevenueRatioFloorBasisPoints : Nat
    depreciationIncludedInDirectCost : Bool
    pureInferenceOnly : Bool
    workloadTokenDenominatorPaid : Bool
    marginalInferenceCostPaid : Bool
    directCostCoordinatePaid : Bool

open CloudDirectCostCoordinate public

irenFY2026CloudCost : CloudDirectCostCoordinate
irenFY2026CloudCost = cloud-direct-cost-coordinate
  "IREN AI Cloud Services" "FY2026" 128795 16932 1314 false false false false true

accountingCoordinatePaid : directCostCoordinatePaid irenFY2026CloudCost ≡ true
accountingCoordinatePaid = refl

ratioFloorIs1314bp : directCostRevenueRatioFloorBasisPoints irenFY2026CloudCost ≡ 1314
ratioFloorIs1314bp = refl

marginalInferenceCostStillOpen : marginalInferenceCostPaid irenFY2026CloudCost ≡ false
marginalInferenceCostStillOpen = refl

data DirectCostRatioEqualsMarginalInferenceCostPermission : Set where
data ExDepreciationCostEqualsFullTCOCostPermission : Set where

directCostRatioDoesNotCreateMarginalCost : DirectCostRatioEqualsMarginalInferenceCostPermission → ⊥
directCostRatioDoesNotCreateMarginalCost ()

exDepreciationCostDoesNotCreateFullTCO : ExDepreciationCostEqualsFullTCOCostPermission → ⊥
exDepreciationCostDoesNotCreateFullTCO ()

boundary : String
boundary =
  "IREN's audited FY2026 segment accounting supplies a provider-side direct-cost coordinate: 16.932 million dollars AI Cloud cost of revenue on 128.795 million dollars AI Cloud Services revenue. DASHI derives only a 1,314 basis-point floor for the direct-cost/revenue ratio using integer arithmetic. The source explicitly excludes depreciation/amortization from this cost-of-revenue line, and the AI Cloud Services segment is broader than a single inference workload. Therefore the coordinate is not a full-TCO margin, not a workload-normalized cost, and not marginal inference cost per token/task."
