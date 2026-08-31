module DASHI.Physics.Closure.NSTriadKNHeatWeightedCommutatorSchurRound301Exact where

------------------------------------------------------------------------
-- ROUND301 / HIGHEST-ALPHA ANALYTIC LEAF:
-- CRITICAL-CONE HEAT-WEIGHTED R294 COMMUTATOR SCHUR
--
-- R300 reduces the nonlinear resolvent remainder to a positive A_s term plus
-- a multiple of ||F_s||^2.  The literal F_s must remain the swap-invariant
-- heat-weighted R294 mixed commutator, not a generic commutator proxy.
--
-- BIDI restriction from R284:
--   deep FL and deep HH are already E*D-payable.  Re-proving them inside a
--   new Schur theorem would strengthen the consumer and duplicate paid work.
--   Therefore this Round301 target is ONLY the unpaid parabolic critical cone
--
--     FL shoulder + HH shoulder + comparable interactions.
--
-- Existing repository x-pollination:
--   * Da Lio--Riviere: genuine three-term compensation precedent, but the
--     repository source audit proves its operator shape is not the literal
--     periodic R294 transport/commutator object.
--   * NSCutoffUniformIntegerShellSchur: exact generic theorem that uniform row
--     and column budgets imply a squared operator bound.
--   * filtered-vortex increment lanes: useful intuition, different residual
--     basis/operator and therefore no direct theorem authority here.
--
-- Highest-alpha physical theorem:
--   realize the CRITICAL-CONE RESTRICTION of F_s on the SAME R294 carrier as a
--   heat-dependent finite kernel; prove cutoff-uniform row/column budgets
--   R_core(s), C_core(s); prove the resulting coefficient is integrable in
--   s,t against already-owned physical input norms.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission

------------------------------------------------------------------------
-- Proof-search dispositions of the candidate x-pollinations.
------------------------------------------------------------------------

daLioThreeTermDirectRoute : Admission.RouteDisposition
daLioThreeTermDirectRoute = Admission.rejected Admission.carrierMismatch

filteredVortexDirectRoute : Admission.RouteDisposition
filteredVortexDirectRoute = Admission.rejected Admission.consumerMismatch

sameObjectCriticalConeHeatSchurRoute : Admission.RouteDisposition
sameObjectCriticalConeHeatSchurRoute = Admission.admitted

------------------------------------------------------------------------
-- Exact analytic target after the existing generic Schur theorem is reused.
------------------------------------------------------------------------

record HeatWeightedCriticalConeCommutatorSchurLeaf : Set where
  constructor heat-weighted-critical-cone-commutator-schur-leaf
  field
    heatParameter : ℚ
    rowBudget columnBudget inputMass outputMass : ℚ

    rowBudgetNonnegative : 0 ≤ rowBudget
    columnBudgetNonnegative : 0 ≤ columnBudget

    literalR294KernelIdentified : Bool
    literalR294KernelIdentifiedIsTrue : literalR294KernelIdentified ≡ true

    criticalConeRestricted : Bool
    criticalConeRestrictedIsTrue : criticalConeRestricted ≡ true

    deepFLAndHHExcludedAsAlreadyPaid : Bool
    deepFLAndHHExcludedAsAlreadyPaidIsTrue :
      deepFLAndHHExcludedAsAlreadyPaid ≡ true

    pointwiseSquaredSchurBound :
      outputMass ≤ (rowBudget * columnBudget) * inputMass

open HeatWeightedCriticalConeCommutatorSchurLeaf public

record HeatWeightedCriticalConeSpacetimePayment : Set where
  constructor heat-weighted-critical-cone-spacetime-payment
  field
    spacetimeForcingMass : ℚ
    spacetimeUpperBound : ℚ
    spacetimeBound : spacetimeForcingMass ≤ spacetimeUpperBound

open HeatWeightedCriticalConeSpacetimePayment public

round301DaLioDirectPromotionRejected : Bool
round301DaLioDirectPromotionRejected = true

round301FilteredVortexDirectPromotionRejected : Bool
round301FilteredVortexDirectPromotionRejected = true

round301SameObjectCriticalConeHeatSchurRouteAdmitted : Bool
round301SameObjectCriticalConeHeatSchurRouteAdmitted = true

round301DeepFLAndHHReprovedInsideSchur : Bool
round301DeepFLAndHHReprovedInsideSchur = false

round301PhysicalCriticalConeHeatKernelRowBudgetClosed : Bool
round301PhysicalCriticalConeHeatKernelRowBudgetClosed = false

round301PhysicalCriticalConeHeatKernelColumnBudgetClosed : Bool
round301PhysicalCriticalConeHeatKernelColumnBudgetClosed = false

round301CriticalConeHeatSchurCoefficientSpacetimeIntegrable : Bool
round301CriticalConeHeatSchurCoefficientSpacetimeIntegrable = false

round301WeightedCriticalConeCommutatorSpacetimePaid : Bool
round301WeightedCriticalConeCommutatorSpacetimePaid = false

round301PackageAClosed : Bool
round301PackageAClosed = false

round301ClayPromotion : Bool
round301ClayPromotion = false

round301SameObjectCriticalConeHeatSchurRouteAdmittedIsTrue :
  round301SameObjectCriticalConeHeatSchurRouteAdmitted ≡ true
round301SameObjectCriticalConeHeatSchurRouteAdmittedIsTrue = refl

round301DeepFLAndHHReprovedInsideSchurIsFalse :
  round301DeepFLAndHHReprovedInsideSchur ≡ false
round301DeepFLAndHHReprovedInsideSchurIsFalse = refl
