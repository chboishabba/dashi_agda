module DASHI.Physics.Closure.NSTriadKNRefinedHeatSchurSearchRound327Exact where

------------------------------------------------------------------------
-- ROUND327 / R301 SEARCH OBSERVER UPDATED TO THE ACTUAL 4 x 4 FRONTIER
--
-- R301 was written before the BIDI refinements of R314 and R316.  Its record
-- still indexes the analytic leaf by the old 3 x 3 observer.  Downstream
-- theorems now distinguish:
--
--   inner:
--     homochiral radial-near
--     homochiral radial-separated
--     heterochiral HH->low
--     heterochiral non-HH
--
--   outer:
--     forcing-low FL
--     forcing-high HL
--     HH
--     comparable.
--
-- This file installs the refined search state without mutating the historical
-- R301 owner.  It also records the first genuinely advanced substate:
-- on the strongly-low heterochiral-HH subcone 3p<=2M, R321--R323 pay all four
-- outer exponent thresholds and R326 supplies the literal physical inner
-- paired-cell low-output bound.  The remaining obligation there is therefore
-- Schur aggregation/spacetime integration, NOT another dyadic gain theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNNestedOuterOrientationRefinementRound314Exact as R314
import DASHI.Physics.Closure.NSTriadKNNestedInnerGeometryRefinementRound316Exact as R316
import DASHI.Physics.Closure.NSTriadKNInnerStrongLowOutputSubconeRound321Exact as R321
import DASHI.Physics.Closure.NSTriadKNStrongLowPaysOuterHHRound323Exact as R323
import DASHI.Physics.Closure.NSTriadKNPhysicalInnerCommutatorLowOutputBoundRound326Exact as R326

data RefinedAnalyticState : Set where
  unresolvedNestedCell : RefinedAnalyticState
  stronglyLowHeterochiralHHCellBound : RefinedAnalyticState
  stronglyLowHeterochiralHHSchurAggregation : RefinedAnalyticState
  stronglyLowHeterochiralHHSpacetimePayment : RefinedAnalyticState
  signedGramPayment : RefinedAnalyticState

data RefinedSearchAction : Set where
  seekNewInnerGeometry : RefinedSearchAction
  useStrongLowInnerCellBound : RefinedSearchAction
  proveNestedRowColumnBudgets : RefinedSearchAction
  integrateHeatSchurCoefficient : RefinedSearchAction

record RefinedNestedHeatSchurLeaf : Set where
  constructor refined-nested-heat-schur-leaf
  field
    innerRoute : R316.RefinedInnerRoute
    outerRegion : R314.OrientedOuterCriticalRegion
    heatParameter : ℚ
    rowBudget columnBudget inputMass outputMass : ℚ
    literalNestedCarrierUsed : Bool
    literalNestedCarrierUsedIsTrue : literalNestedCarrierUsed ≡ true

open RefinedNestedHeatSchurLeaf public

-- The strongly-low heterochiral-HH branch has already crossed the exponent and
-- cell-level physical gates.  Do not reopen them during Schur search.
stronglyLowHeterochiralHHRouteDisposition : Admission.RouteDisposition
stronglyLowHeterochiralHHRouteDisposition = Admission.admitted

round327OldThreeByThreeObserverSufficient : Bool
round327OldThreeByThreeObserverSufficient = false

round327RefinedFourByFourObserverInstalled : Bool
round327RefinedFourByFourObserverInstalled = true

round327StrongLowHeterochiralHHAllOuterExponentCellsPaid : Bool
round327StrongLowHeterochiralHHAllOuterExponentCellsPaid =
  R323.round323StronglyLowPaysAllFourHeterochiralHHOuterExponentCells

round327StrongLowHeterochiralHHPhysicalInnerCellBoundClosed : Bool
round327StrongLowHeterochiralHHPhysicalInnerCellBoundClosed =
  R326.round326PhysicalR120R178SameObjectBoundClosed

round327StrongLowHeterochiralHHNeedsAnotherGainTheorem : Bool
round327StrongLowHeterochiralHHNeedsAnotherGainTheorem = false

round327StrongLowHeterochiralHHSchurAggregationClosed : Bool
round327StrongLowHeterochiralHHSchurAggregationClosed = false

round327StrongLowHeterochiralHHSpacetimePaid : Bool
round327StrongLowHeterochiralHHSpacetimePaid = false

round327PackageAClosed : Bool
round327PackageAClosed = false

round327ClayPromotion : Bool
round327ClayPromotion = false

round327PackageAClosedIsFalse : round327PackageAClosed ≡ false
round327PackageAClosedIsFalse = refl

round327ClayPromotionIsFalse : round327ClayPromotion ≡ false
round327ClayPromotionIsFalse = refl
