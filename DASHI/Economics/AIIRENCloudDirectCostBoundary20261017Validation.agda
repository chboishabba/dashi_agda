module DASHI.Economics.AIIRENCloudDirectCostBoundary20261017Validation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Economics.AIIRENCloudDirectCostBoundary20261017Exact as Cost

accountingCoordinatePaid : Cost.directCostCoordinatePaid Cost.irenFY2026CloudCost ≡ true
accountingCoordinatePaid = Cost.accountingCoordinatePaid

ratioFloorPaid : Cost.directCostRevenueRatioFloorBasisPoints Cost.irenFY2026CloudCost ≡ 1314
ratioFloorPaid = Cost.ratioFloorIs1314bp

marginalCostStillOpen : Cost.marginalInferenceCostPaid Cost.irenFY2026CloudCost ≡ false
marginalCostStillOpen = Cost.marginalInferenceCostStillOpen
