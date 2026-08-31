module DASHI.Physics.Closure.NSTriadKNCriticalConeProofSearchRefinementRound308Exact where

------------------------------------------------------------------------
-- ROUND308 / PROOF-SEARCH REFINEMENT AFTER THE HEAT-EXPONENT DIAGNOSTIC
--
-- Learned feedback:
--
--   R305: one parabolic heat/resolvent payment leaves the exact R234/R235
--         shoulder exponents; heat alone is not the missing critical gain.
--
--   R306: the R230 forcing is a helicity commutator, not generically the R120
--         scalar multiplier-difference commutator.
--
--   R307: on a transverse forcing/velocity pair the doubled R230 cell is the
--         existing R167 normalized-direction slot kernel with first amplitude
--         equal to the physical projected nonlinearity N_p.
--
-- Therefore the admitted next route is not another global Schur bound.  It is
-- to expand
--
--   N_p = sum_{a+b=p} projectedOrderedTerm(a,b)
--
-- inside the R307 outer slot kernel and classify the nested resonant geometry
--
--   a+b=p,  p+q=k
--
-- before norms.  This is the smallest same-object producer capable of showing
-- which subcone actually carries the remaining heat-Schur singularity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission

data CriticalConeSubproblem : Set where
  flShoulder hhShoulder comparable : CriticalConeSubproblem

data RefinementState : Set where
  heatOnlyDiagnostic
  scalarCommutatorReuse
  outerHelicitySlotKernel
  nestedProjectedNonlinearity
  rowColumnShellBudget
  spacetimePayment : RefinementState

heatOnlyRoute : Admission.RouteDisposition
heatOnlyRoute = Admission.rejected Admission.strengthMismatch

r120ScalarCommutatorDirectRoute : Admission.RouteDisposition
r120ScalarCommutatorDirectRoute = Admission.rejected Admission.carrierMismatch

r307OuterSlotKernelRoute : Admission.RouteDisposition
r307OuterSlotKernelRoute = Admission.admitted

nestedTriadExpansionRoute : Admission.RouteDisposition
nestedTriadExpansionRoute = Admission.admitted

record NestedTriadFrontier : Set where
  constructor nested-triad-frontier
  field
    subproblem : CriticalConeSubproblem

    -- Exact resonance architecture to be inhabited by the physical producer.
    innerOutputIsOuterLeftMode : Bool
    outerOutputPreserved : Bool

    -- The next theorem must keep the exact R307 slot-kernel carrier and expand
    -- only its first amplitude through the literal projectedNonlinearity fold.
    sameOuterSlotKernel : Bool
    literalInnerGalerkinFibre : Bool

    innerOutputIsOuterLeftModeIsTrue : innerOutputIsOuterLeftMode ≡ true
    outerOutputPreservedIsTrue : outerOutputPreserved ≡ true
    sameOuterSlotKernelIsTrue : sameOuterSlotKernel ≡ true
    literalInnerGalerkinFibreIsTrue : literalInnerGalerkinFibre ≡ true

open NestedTriadFrontier public

round308HeatOnlyRouteRejected : Bool
round308HeatOnlyRouteRejected = true

round308R120DirectReuseRejected : Bool
round308R120DirectReuseRejected = true

round308R307NestedTriadRouteAdmitted : Bool
round308R307NestedTriadRouteAdmitted = true

round308NestedSlotKernelExpansionClosed : Bool
round308NestedSlotKernelExpansionClosed = false

round308CriticalConeRowColumnBudgetsClosed : Bool
round308CriticalConeRowColumnBudgetsClosed = false

round308PackageAClosed : Bool
round308PackageAClosed = false

round308ClayPromotion : Bool
round308ClayPromotion = false

round308R307NestedTriadRouteAdmittedIsTrue :
  round308R307NestedTriadRouteAdmitted ≡ true
round308R307NestedTriadRouteAdmittedIsTrue = refl
