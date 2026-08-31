module DASHI.Physics.Closure.NSTriadKNNestedOuterOrientationRefinementRound314Exact where

------------------------------------------------------------------------
-- ROUND314 / BIDI CORRECTION: OUTER FL/HL ORIENTATION IS THEOREM-RELEVANT
--
-- R313 proposed a 3 x 3 diagnostic matrix using one combined outer FL
-- shoulder.  That is sufficient for the symmetric quadratic companion, but
-- it is too coarse for the R230/R307 forcing object:
--
--   F_pq = G_p+ x u_q- - G_p- x u_q+.
--
-- The nonlinear forcing G_p sits specifically on the p leg.  Since the inner
-- nested fibre a+b=p lives INSIDE G_p, an outer low/high interaction must keep
-- track of whether p is the low leg or the high leg.  Collapsing LH and HL
-- would erase exactly where the nested inner gain is inserted.
--
-- Hence the correct proof-search matrix is 3 inner routes x 4 outer oriented
-- regions, not 3 x 3:
--
--   forcing-low FL shoulder   : p low,  q high
--   forcing-high HL shoulder  : p high, q low
--   HH output shoulder
--   comparable
--
-- No shell estimate is asserted here.  This is an observer refinement forced
-- by the exact downstream consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311

data OrientedOuterCriticalRegion : Set where
  forcingLowFLShoulder : OrientedOuterCriticalRegion
  forcingHighHLShoulder : OrientedOuterCriticalRegion
  outerHHShoulder : OrientedOuterCriticalRegion
  outerComparable : OrientedOuterCriticalRegion

record OrientedNestedRoute : Set where
  constructor oriented-nested-route
  field
    innerRoute : R311.InnerNestedRoute
    outerRegion : OrientedOuterCriticalRegion

open OrientedNestedRoute public

routeDisposition : OrientedNestedRoute → Admission.RouteDisposition
routeDisposition route = Admission.admitted

-- The finite search surface has twelve semantically distinct route cells.
data TwelveCellIndex : Set where
  nearLow nearHigh nearHH nearCC : TwelveCellIndex
  separatedLow separatedHigh separatedHH separatedCC : TwelveCellIndex
  heteroLow heteroHigh heteroHH heteroCC : TwelveCellIndex

indexRoute : TwelveCellIndex → OrientedNestedRoute
indexRoute nearLow = oriented-nested-route R311.homochiralRadialNear forcingLowFLShoulder
indexRoute nearHigh = oriented-nested-route R311.homochiralRadialNear forcingHighHLShoulder
indexRoute nearHH = oriented-nested-route R311.homochiralRadialNear outerHHShoulder
indexRoute nearCC = oriented-nested-route R311.homochiralRadialNear outerComparable
indexRoute separatedLow = oriented-nested-route R311.homochiralRadialSeparated forcingLowFLShoulder
indexRoute separatedHigh = oriented-nested-route R311.homochiralRadialSeparated forcingHighHLShoulder
indexRoute separatedHH = oriented-nested-route R311.homochiralRadialSeparated outerHHShoulder
indexRoute separatedCC = oriented-nested-route R311.homochiralRadialSeparated outerComparable
indexRoute heteroLow = oriented-nested-route R311.heterochiral forcingLowFLShoulder
indexRoute heteroHigh = oriented-nested-route R311.heterochiral forcingHighHLShoulder
indexRoute heteroHH = oriented-nested-route R311.heterochiral outerHHShoulder
indexRoute heteroCC = oriented-nested-route R311.heterochiral outerComparable

round314CombinedFLObserverTooCoarseForNestedForcing : Bool
round314CombinedFLObserverTooCoarseForNestedForcing = true

round314ForcingLegOrientationRetained : Bool
round314ForcingLegOrientationRetained = true

round314DiagnosticCellCountIsTwelve : Bool
round314DiagnosticCellCountIsTwelve = true

round314AnyTwelveCellExponentComputed : Bool
round314AnyTwelveCellExponentComputed = false

round314PackageAClosed : Bool
round314PackageAClosed = false

round314ClayPromotion : Bool
round314ClayPromotion = false

round314CombinedFLObserverTooCoarseForNestedForcingIsTrue :
  round314CombinedFLObserverTooCoarseForNestedForcing ≡ true
round314CombinedFLObserverTooCoarseForNestedForcingIsTrue = refl

round314PackageAClosedIsFalse : round314PackageAClosed ≡ false
round314PackageAClosedIsFalse = refl
