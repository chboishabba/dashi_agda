module DASHI.Physics.Closure.NSTriadKNHeatWeightedCommutatorSchurRound301Exact where

------------------------------------------------------------------------
-- ROUND301 / HIGHEST-ALPHA ANALYTIC LEAF:
-- NESTED CRITICAL-CONE HEAT-WEIGHTED R294 COMMUTATOR SCHUR
--
-- R300 reduces the nonlinear resolvent remainder to a positive A_s term plus
-- a multiple of ||F_s||^2.  The literal F_s must remain the swap-invariant
-- heat-weighted R294 mixed commutator, not a generic commutator proxy.
--
-- BIDI restriction from R284:
--   deep FL and deep HH are already E*D-payable.  Re-proving them inside a
--   new Schur theorem would strengthen the consumer and duplicate paid work.
--
-- R305 then proves heat-only power counting does NOT pay the critical cone.
-- R306--R310 expose additional signed structure before norms:
--
--   outer R307 slot/null kernel on (p,q),
--   inner physical Galerkin fibre a+b=p,
--   inner a/b swap pairing to the R120 multiplier-difference commutator.
--
-- R311 shows the inner multiplier difference is a genuine small factor only
-- on radial-near homochiral interactions.  R312 identifies a complementary
-- heterochiral HH->low candidate: inner high derivative times inner null gain
-- relocates to the inner output p at the exponent level.
--
-- Therefore R301 is no longer one monolithic heat-Schur theorem.  The live
-- analytic search is the finite nested route matrix
--
--   {homochiral-near, homochiral-separated, heterochiral}
--      x {outer-FL-shoulder, outer-HH-shoulder, outer-comparable}.
--
-- Row/column shell exponents must be computed separately for these children.
-- A failing child may request extra signed/null geometry without strengthening
-- the successful children.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNNestedCriticalConeShellKernelRound313Exact as R313

------------------------------------------------------------------------
-- Proof-search dispositions of the candidate x-pollinations.
------------------------------------------------------------------------

daLioThreeTermDirectRoute : Admission.RouteDisposition
daLioThreeTermDirectRoute = Admission.rejected Admission.carrierMismatch

filteredVortexDirectRoute : Admission.RouteDisposition
filteredVortexDirectRoute = Admission.rejected Admission.consumerMismatch

sameObjectNestedCriticalConeHeatSchurRoute : Admission.RouteDisposition
sameObjectNestedCriticalConeHeatSchurRoute = Admission.admitted

------------------------------------------------------------------------
-- Exact analytic target after the existing generic Schur theorem is reused.
------------------------------------------------------------------------

record HeatWeightedNestedCriticalConeCommutatorSchurLeaf : Set where
  constructor heat-weighted-nested-critical-cone-commutator-schur-leaf
  field
    heatParameter : ℚ
    innerRoute : R311.InnerNestedRoute
    outerSubcone : R313.OuterCriticalSubcone
    rowBudget columnBudget inputMass outputMass : ℚ

    rowBudgetNonnegative : 0 ≤ rowBudget
    columnBudgetNonnegative : 0 ≤ columnBudget

    literalR294KernelIdentified : Bool
    literalR294KernelIdentifiedIsTrue : literalR294KernelIdentified ≡ true

    nestedR309R310CarrierUsed : Bool
    nestedR309R310CarrierUsedIsTrue : nestedR309R310CarrierUsed ≡ true

    deepFLAndHHExcludedAsAlreadyPaid : Bool
    deepFLAndHHExcludedAsAlreadyPaidIsTrue :
      deepFLAndHHExcludedAsAlreadyPaid ≡ true

    pointwiseSquaredSchurBound :
      outputMass ≤ (rowBudget * columnBudget) * inputMass

open HeatWeightedNestedCriticalConeCommutatorSchurLeaf public

record HeatWeightedNestedCriticalConeSpacetimePayment : Set where
  constructor heat-weighted-nested-critical-cone-spacetime-payment
  field
    spacetimeForcingMass : ℚ
    spacetimeUpperBound : ℚ
    spacetimeBound : spacetimeForcingMass ≤ spacetimeUpperBound

open HeatWeightedNestedCriticalConeSpacetimePayment public

round301DaLioDirectPromotionRejected : Bool
round301DaLioDirectPromotionRejected = true

round301FilteredVortexDirectPromotionRejected : Bool
round301FilteredVortexDirectPromotionRejected = true

round301SameObjectNestedCriticalConeHeatSchurRouteAdmitted : Bool
round301SameObjectNestedCriticalConeHeatSchurRouteAdmitted = true

round301DeepFLAndHHReprovedInsideSchur : Bool
round301DeepFLAndHHReprovedInsideSchur = false

round301NestedRouteMatrixRequired : Bool
round301NestedRouteMatrixRequired = true

round301PhysicalNestedHeatKernelRowBudgetClosed : Bool
round301PhysicalNestedHeatKernelRowBudgetClosed = false

round301PhysicalNestedHeatKernelColumnBudgetClosed : Bool
round301PhysicalNestedHeatKernelColumnBudgetClosed = false

round301NestedHeatSchurCoefficientSpacetimeIntegrable : Bool
round301NestedHeatSchurCoefficientSpacetimeIntegrable = false

round301WeightedNestedCommutatorSpacetimePaid : Bool
round301WeightedNestedCommutatorSpacetimePaid = false

round301PackageAClosed : Bool
round301PackageAClosed = false

round301ClayPromotion : Bool
round301ClayPromotion = false

round301SameObjectNestedCriticalConeHeatSchurRouteAdmittedIsTrue :
  round301SameObjectNestedCriticalConeHeatSchurRouteAdmitted ≡ true
round301SameObjectNestedCriticalConeHeatSchurRouteAdmittedIsTrue = refl

round301DeepFLAndHHReprovedInsideSchurIsFalse :
  round301DeepFLAndHHReprovedInsideSchur ≡ false
round301DeepFLAndHHReprovedInsideSchurIsFalse = refl
