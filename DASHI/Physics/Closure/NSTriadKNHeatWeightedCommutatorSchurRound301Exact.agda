module DASHI.Physics.Closure.NSTriadKNHeatWeightedCommutatorSchurRound301Exact where

------------------------------------------------------------------------
-- ROUND301 / NESTED CRITICAL-CONE HEAT-WEIGHTED R294 COMMUTATOR SCHUR
--
-- R300 reduces the nonlinear resolvent remainder to a positive A_s term plus
-- a multiple of ||F_s||^2. The literal F_s must remain the swap-invariant
-- heat-weighted R294 mixed commutator, not a generic commutator proxy.
--
-- STATUS CORRECTION AFTER R342--R355 AND R434--R437
-- -------------------------------------------------
-- The original R301 prose said deep FL and deep HH were already E*D-payable.
-- R434 now records the correct distinction: R234/R235 own the relevant scalar
-- exponent/null-gain compilers, but their literal physical shell/convolution
-- welds remain open. R284 is therefore a conditional decomposition route, not
-- a source of globally inhabited deep-region payments.
--
-- This does not make R284 mandatory for the direct R423 target. It only means
-- that a proof choosing THIS critical-cone Schur decomposition must provide its
-- own physical region payments honestly.
--
-- R306--R310 expose signed structure before norms:
--
--   outer R307 slot/null kernel on (p,q),
--   inner physical Galerkin fibre a+b=p,
--   inner a/b swap pairing to the R120 multiplier-difference commutator.
--
-- R435 makes one previously implicit inner structural step proof-bearing:
-- under the SAME all-inner-helical witness required by R310,
--
--   K(P,Q,N_p+N_p,v)
--     = fold_{a+b=p} K(P,Q,pureCommutator_ab,v).
--
-- R436/R437 close the distinct outer orientation seam WITHOUT any all-inner-
-- helical assumption. On an all-mode transverse physical velocity field every
-- projected-forcing outer cell is classified exactly as either
--
--   p != 0 : the literal R307/R167 slot-kernel identity, or
--   p  = 0 : projectedNonlinearity(p)=0 and the doubled R230 cell is zero.
--
-- Thus normalizedDirection is never requested at zero and the old p=0
-- exception is removed before norms. This still does not pay the weighted R294
-- fold or the R423 spacetime budget.
--
-- R311/R312 split the inner geometry. Later R314--R327 refine the search to the
-- oriented 4 x 4 route matrix and close the strongly-low heterochiral-HH
-- exponent/cell-level gates. R342--R355 subsequently close the generic finite
-- incidence, weighted-Schur, resolvent, signed-flux and Package-A COMPILERS.
-- Those later owners depend downstream on R301, so they are documented here
-- but deliberately NOT imported back into this owner. The remaining Schur
-- content is physical: instantiate the literal finite row/column inequalities
-- and a cutoff-uniform spacetime forcing payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNNestedCriticalConeShellKernelRound313Exact as R313
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedFiniteSchurCertificateRound346Exact as R346
import DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeCompilerRound434Exact as R434
import DASHI.Physics.Closure.NSTriadKNNestedInnerForcingAggregationRound435Exact as R435
import DASHI.Physics.Closure.NSTriadKNProjectedForcingOuterCellExhaustiveRound437Exact as R437

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

    -- Historical compatibility field. In this route it means the leaf is
    -- scoped to the R284 critical-cone branch. It must NOT be read as a proof
    -- that the deep FL/HH physical welds are globally inhabited.
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

round301R435InnerAggregationBridgeClosed : Bool
round301R435InnerAggregationBridgeClosed =
  R435.round435InnerPureCommutatorAggregationThroughOuterSlotClosed

round301R435AllInnerHelicalTrajectoryWeldClosed : Bool
round301R435AllInnerHelicalTrajectoryWeldClosed =
  R435.round435ArbitraryPhysicalTrajectoryAllInnerHelicalWeldClosed

round301ProjectedForcingOuterCellsExhaustivelySlotOrZero : Bool
round301ProjectedForcingOuterCellsExhaustivelySlotOrZero =
  R437.round437EveryOuterCellClassifiedSlotOrZero

round301ZeroForcingLegDiscardedBeforeNorm : Bool
round301ZeroForcingLegDiscardedBeforeNorm =
  R437.round437ZeroForcingLegDiscardedBeforeNorm

round301NormalizedDirectionAtZeroRequired : Bool
round301NormalizedDirectionAtZeroRequired =
  R437.round437NormalizedDirectionAtZeroRequired

round301DeepFarLowPhysicalWeldClosed : Bool
round301DeepFarLowPhysicalWeldClosed =
  R434.round434DeepFarLowPhysicalWeldClosed

round301DeepHighHighPhysicalWeldClosed : Bool
round301DeepHighHighPhysicalWeldClosed =
  R434.round434DeepHighHighPhysicalWeldClosed

round301DeepFLAndHHReprovedInsideSchur : Bool
round301DeepFLAndHHReprovedInsideSchur = false

round301NestedRouteMatrixRequired : Bool
round301NestedRouteMatrixRequired = true

round301FiniteSchurPackagingAlreadyOwned : Bool
round301FiniteSchurPackagingAlreadyOwned =
  R346.round346FiniteSchurPackagingClosed

round301PhysicalNestedHeatKernelRowBudgetClosed : Bool
round301PhysicalNestedHeatKernelRowBudgetClosed = false

round301PhysicalNestedHeatKernelColumnBudgetClosed : Bool
round301PhysicalNestedHeatKernelColumnBudgetClosed = false

round301NestedHeatSchurCoefficientSpacetimeIntegrable : Bool
round301NestedHeatSchurCoefficientSpacetimeIntegrable = false

round301RemainingSchurContentIsPhysicalRowColumnPlusSpacetime : Bool
round301RemainingSchurContentIsPhysicalRowColumnPlusSpacetime = true

round301WeightedNestedCommutatorSpacetimePaid : Bool
round301WeightedNestedCommutatorSpacetimePaid = false

round301PackageAClosed : Bool
round301PackageAClosed = false

round301ClayPromotion : Bool
round301ClayPromotion = false

round301SameObjectNestedCriticalConeHeatSchurRouteAdmittedIsTrue :
  round301SameObjectNestedCriticalConeHeatSchurRouteAdmitted ≡ true
round301SameObjectNestedCriticalConeHeatSchurRouteAdmittedIsTrue = refl

round301R435InnerAggregationBridgeClosedIsTrue :
  round301R435InnerAggregationBridgeClosed ≡ true
round301R435InnerAggregationBridgeClosedIsTrue =
  R435.round435InnerPureCommutatorAggregationThroughOuterSlotClosedIsTrue

round301R435AllInnerHelicalTrajectoryWeldClosedIsFalse :
  round301R435AllInnerHelicalTrajectoryWeldClosed ≡ false
round301R435AllInnerHelicalTrajectoryWeldClosedIsFalse =
  R435.round435ArbitraryPhysicalTrajectoryAllInnerHelicalWeldClosedIsFalse

round301ProjectedForcingOuterCellsExhaustivelySlotOrZeroIsTrue :
  round301ProjectedForcingOuterCellsExhaustivelySlotOrZero ≡ true
round301ProjectedForcingOuterCellsExhaustivelySlotOrZeroIsTrue =
  R437.round437EveryOuterCellClassifiedSlotOrZeroIsTrue

round301NormalizedDirectionAtZeroRequiredIsFalse :
  round301NormalizedDirectionAtZeroRequired ≡ false
round301NormalizedDirectionAtZeroRequiredIsFalse =
  R437.round437NormalizedDirectionAtZeroRequiredIsFalse

round301DeepFarLowPhysicalWeldClosedIsFalse :
  round301DeepFarLowPhysicalWeldClosed ≡ false
round301DeepFarLowPhysicalWeldClosedIsFalse =
  R434.round434DeepFarLowPhysicalWeldClosedIsFalse

round301DeepHighHighPhysicalWeldClosedIsFalse :
  round301DeepHighHighPhysicalWeldClosed ≡ false
round301DeepHighHighPhysicalWeldClosedIsFalse =
  R434.round434DeepHighHighPhysicalWeldClosedIsFalse

round301FiniteSchurPackagingAlreadyOwnedIsTrue :
  round301FiniteSchurPackagingAlreadyOwned ≡ true
round301FiniteSchurPackagingAlreadyOwnedIsTrue =
  R346.round346FiniteSchurPackagingClosedIsTrue

round301DeepFLAndHHReprovedInsideSchurIsFalse :
  round301DeepFLAndHHReprovedInsideSchur ≡ false
round301DeepFLAndHHReprovedInsideSchurIsFalse = refl

round301RemainingSchurContentIsPhysicalRowColumnPlusSpacetimeIsTrue :
  round301RemainingSchurContentIsPhysicalRowColumnPlusSpacetime ≡ true
round301RemainingSchurContentIsPhysicalRowColumnPlusSpacetimeIsTrue = refl
