module DASHI.Physics.Closure.NSTriadKNHeatWeightedCommutatorSchurRound301Exact where

------------------------------------------------------------------------
-- ROUND301 / HIGHEST-ALPHA ANALYTIC LEAF: HEAT-WEIGHTED R294 COMMUTATOR SCHUR
--
-- R300 reduces the nonlinear resolvent remainder to a positive A_s term plus
-- a multiple of ||F_s||^2.  The literal F_s must remain the swap-invariant
-- heat-weighted R294 mixed commutator, not a generic commutator proxy.
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
-- Therefore the highest-alpha physical theorem is sharpened to:
--
--   realize F_s on the SAME R294 carrier as a heat-dependent finite kernel;
--   prove cutoff-uniform row/column budgets R(s),C(s);
--   prove the resulting Schur coefficient is integrable in s,t against the
--   already-owned physical input norms.
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

sameObjectHeatSchurRoute : Admission.RouteDisposition
sameObjectHeatSchurRoute = Admission.admitted

------------------------------------------------------------------------
-- Exact analytic target after the existing generic Schur theorem is reused.
------------------------------------------------------------------------

record HeatWeightedCommutatorSchurLeaf : Set where
  constructor heat-weighted-commutator-schur-leaf
  field
    -- s-dependent Schur budgets for the literal heat-weighted R294 kernel.
    heatParameter : ℚ
    rowBudget columnBudget inputMass outputMass : ℚ

    rowBudgetNonnegative : 0 ≤ rowBudget
    columnBudgetNonnegative : 0 ≤ columnBudget

    -- Same-object identification: the kernel action here is the actual R294
    -- weighted mixed commutator, not merely an analogous operator.
    literalR294KernelIdentified : Bool
    literalR294KernelIdentifiedIsTrue : literalR294KernelIdentified ≡ true

    -- Produced by the existing uniform Schur theorem once row/column estimates
    -- for that literal kernel are instantiated.
    pointwiseSquaredSchurBound :
      outputMass ≤ (rowBudget * columnBudget) * inputMass

open HeatWeightedCommutatorSchurLeaf public

record HeatWeightedCommutatorSpacetimePayment : Set where
  constructor heat-weighted-commutator-spacetime-payment
  field
    spacetimeForcingMass : ℚ
    spacetimeUpperBound : ℚ
    spacetimeBound : spacetimeForcingMass ≤ spacetimeUpperBound

open HeatWeightedCommutatorSpacetimePayment public

round301DaLioDirectPromotionRejected : Bool
round301DaLioDirectPromotionRejected = true

round301FilteredVortexDirectPromotionRejected : Bool
round301FilteredVortexDirectPromotionRejected = true

round301SameObjectHeatSchurRouteAdmitted : Bool
round301SameObjectHeatSchurRouteAdmitted = true

round301PhysicalHeatKernelRowBudgetClosed : Bool
round301PhysicalHeatKernelRowBudgetClosed = false

round301PhysicalHeatKernelColumnBudgetClosed : Bool
round301PhysicalHeatKernelColumnBudgetClosed = false

round301HeatSchurCoefficientSpacetimeIntegrable : Bool
round301HeatSchurCoefficientSpacetimeIntegrable = false

round301WeightedCommutatorSpacetimePaid : Bool
round301WeightedCommutatorSpacetimePaid = false

round301PackageAClosed : Bool
round301PackageAClosed = false

round301ClayPromotion : Bool
round301ClayPromotion = false

round301SameObjectHeatSchurRouteAdmittedIsTrue :
  round301SameObjectHeatSchurRouteAdmitted ≡ true
round301SameObjectHeatSchurRouteAdmittedIsTrue = refl
