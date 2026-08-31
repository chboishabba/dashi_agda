module DASHI.Physics.Closure.NSTriadKNNestedInnerGeometryRefinementRound316Exact where

------------------------------------------------------------------------
-- ROUND316 / BIDI REFINEMENT OF THE INNER HETEROCHIRAL ROUTE
--
-- R311 correctly separates homochiral radial-near, homochiral radial-separated
-- and heterochiral multiplier behaviour.  R312 then discovers a new theorem-
-- relevant distinction INSIDE the heterochiral fibre: derivative relocation
-- from the inner high scale to the inner output scale requires an inner
-- heterochiral HH->low configuration a+b=p.
--
-- Therefore the single R311 heterochiral observer is too coarse for the R312
-- consumer.  This owner refines it without changing R311:
--
--   homochiral radial-near
--   homochiral radial-separated
--   heterochiral HH->low
--   heterochiral non-HH
--
-- Combined with R314's four oriented outer regions, the live diagnostic
-- surface has sixteen cells.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNNestedOuterOrientationRefinementRound314Exact as R314

data RefinedInnerRoute : Set where
  homochiralRadialNear : RefinedInnerRoute
  homochiralRadialSeparated : RefinedInnerRoute
  heterochiralHHToLow : RefinedInnerRoute
  heterochiralNonHH : RefinedInnerRoute

forgetInnerRefinement : RefinedInnerRoute → R311.InnerNestedRoute
forgetInnerRefinement homochiralRadialNear = R311.homochiralRadialNear
forgetInnerRefinement homochiralRadialSeparated = R311.homochiralRadialSeparated
forgetInnerRefinement heterochiralHHToLow = R311.heterochiralInner
forgetInnerRefinement heterochiralNonHH = R311.heterochiralInner

innerRouteDisposition : RefinedInnerRoute → Admission.RouteDisposition
innerRouteDisposition homochiralRadialNear = Admission.admitted
innerRouteDisposition homochiralRadialSeparated = Admission.redirectedReuse
innerRouteDisposition heterochiralHHToLow = Admission.admitted
innerRouteDisposition heterochiralNonHH = Admission.redirectedReuse

record RefinedNestedRoute : Set where
  constructor refined-nested-route
  field
    innerRoute : RefinedInnerRoute
    outerRegion : R314.OrientedOuterCriticalRegion

open RefinedNestedRoute public

data SixteenCellIndex : Set where
  nearLow nearHigh nearHH nearCC : SixteenCellIndex
  separatedLow separatedHigh separatedHH separatedCC : SixteenCellIndex
  heteroHHInnerLow heteroHHInnerHigh heteroHHInnerOuterHH heteroHHInnerCC : SixteenCellIndex
  heteroOtherLow heteroOtherHigh heteroOtherHH heteroOtherCC : SixteenCellIndex

indexRoute : SixteenCellIndex → RefinedNestedRoute
indexRoute nearLow = refined-nested-route homochiralRadialNear R314.forcingLowFLShoulder
indexRoute nearHigh = refined-nested-route homochiralRadialNear R314.forcingHighHLShoulder
indexRoute nearHH = refined-nested-route homochiralRadialNear R314.outerHHShoulder
indexRoute nearCC = refined-nested-route homochiralRadialNear R314.outerComparable
indexRoute separatedLow = refined-nested-route homochiralRadialSeparated R314.forcingLowFLShoulder
indexRoute separatedHigh = refined-nested-route homochiralRadialSeparated R314.forcingHighHLShoulder
indexRoute separatedHH = refined-nested-route homochiralRadialSeparated R314.outerHHShoulder
indexRoute separatedCC = refined-nested-route homochiralRadialSeparated R314.outerComparable
indexRoute heteroHHInnerLow = refined-nested-route heterochiralHHToLow R314.forcingLowFLShoulder
indexRoute heteroHHInnerHigh = refined-nested-route heterochiralHHToLow R314.forcingHighHLShoulder
indexRoute heteroHHInnerOuterHH = refined-nested-route heterochiralHHToLow R314.outerHHShoulder
indexRoute heteroHHInnerCC = refined-nested-route heterochiralHHToLow R314.outerComparable
indexRoute heteroOtherLow = refined-nested-route heterochiralNonHH R314.forcingLowFLShoulder
indexRoute heteroOtherHigh = refined-nested-route heterochiralNonHH R314.forcingHighHLShoulder
indexRoute heteroOtherHH = refined-nested-route heterochiralNonHH R314.outerHHShoulder
indexRoute heteroOtherCC = refined-nested-route heterochiralNonHH R314.outerComparable

round316R311HeterochiralObserverTooCoarseForR312 : Bool
round316R311HeterochiralObserverTooCoarseForR312 = true

round316HHToLowRelocationRouteSeparated : Bool
round316HHToLowRelocationRouteSeparated = true

round316DiagnosticCellCountIsSixteen : Bool
round316DiagnosticCellCountIsSixteen = true

round316R312GainPromotedToAllHeterochiralInteractions : Bool
round316R312GainPromotedToAllHeterochiralInteractions = false

round316AnySixteenCellPhysicalExponentClosed : Bool
round316AnySixteenCellPhysicalExponentClosed = false

round316PackageAClosed : Bool
round316PackageAClosed = false

round316ClayPromotion : Bool
round316ClayPromotion = false

round316PackageAClosedIsFalse : round316PackageAClosed ≡ false
round316PackageAClosedIsFalse = refl
