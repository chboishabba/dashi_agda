module DASHI.Physics.Closure.NSTriadKNSixteenCellThresholdSearchRound318Exact where

------------------------------------------------------------------------
-- ROUND318 / THRESHOLD SURFACES FOR THE SIXTEEN-CELL SEARCH
--
-- R317 computes the currently-known symbolic gain per refined inner route.
-- This owner turns those formulas into the exact backward threshold consumed
-- by R315.  It does NOT assert that any physical threshold is satisfied.
--
-- Existing candidate mechanisms:
--
--   homochiral radial-near:
--     missingOuterGain <= 2 * radialNearAmplitudeGain
--
--   heterochiral HH->low:
--     missingOuterGain <= 2 * (innerHHHighShell - pShell)
--
-- Routes with no currently-owned extra inner gain must instead prove the bare
-- heat residual nonpositive, which is incompatible with the intended strict
-- critical region and therefore signals a need for NEW GEOMETRY rather than
-- more algebraic repackaging.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Rational.Base as ℚ
open ℚ using (ℚ; _-_; _*_; _≤_)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNNestedCriticalGainConsumerRound315Exact as R315
import DASHI.Physics.Closure.NSTriadKNNestedInnerGeometryRefinementRound316Exact as R316
import DASHI.Physics.Closure.NSTriadKNSixteenCellKnownGainDiagnosticRound317Exact as R317

two : ℚ
two = 2

record NearHomochiralThreshold : Set where
  constructor near-homochiral-threshold
  field
    route : R316.RefinedNestedRoute
    parameters : R317.KnownGainParameters
    routeIsNear : R316.innerRoute route ≡ R316.homochiralRadialNear
    threshold :
      R315.missingSquaredGain (R316.outerRegion route) (R317.shells parameters)
      ≤ two * R317.radialNearAmplitudeGain parameters

open NearHomochiralThreshold public

record HeterochiralHHThreshold : Set where
  constructor heterochiral-hh-threshold
  field
    route : R316.RefinedNestedRoute
    parameters : R317.KnownGainParameters
    routeIsHHRelocation : R316.innerRoute route ≡ R316.heterochiralHHToLow
    threshold :
      R315.missingSquaredGain (R316.outerRegion route) (R317.shells parameters)
      ≤ two *
          (R317.innerHHHighShell parameters
            - R315.pShell (R317.shells parameters))

open HeterochiralHHThreshold public

-- For the other route families the currently-owned mechanism contributes no
-- additional squared gain.  Any progress must therefore come from a new
-- signed/null/orthogonality theorem rather than reusing R310/R312 alone.
data ExistingMechanismClass : R316.RefinedInnerRoute → Set where
  nearMechanism : ExistingMechanismClass R316.homochiralRadialNear
  hhRelocationMechanism : ExistingMechanismClass R316.heterochiralHHToLow

data NeedsNewGeometryClass : R316.RefinedInnerRoute → Set where
  separatedNeedsNewGeometry :
    NeedsNewGeometryClass R316.homochiralRadialSeparated
  heterochiralNonHHNeedsNewGeometry :
    NeedsNewGeometryClass R316.heterochiralNonHH

searchDisposition : R316.RefinedInnerRoute → Admission.RouteDisposition
searchDisposition R316.homochiralRadialNear = Admission.admitted
searchDisposition R316.homochiralRadialSeparated = Admission.redirectedReuse
searchDisposition R316.heterochiralHHToLow = Admission.admitted
searchDisposition R316.heterochiralNonHH = Admission.redirectedReuse

round318NearThresholdSurfaceInstalled : Bool
round318NearThresholdSurfaceInstalled = true

round318HeterochiralHHThresholdSurfaceInstalled : Bool
round318HeterochiralHHThresholdSurfaceInstalled = true

round318EightCellsHaveExistingCandidateMechanism : Bool
round318EightCellsHaveExistingCandidateMechanism = true

round318OtherEightCellsNeedNewGeometry : Bool
round318OtherEightCellsNeedNewGeometry = true

round318AnyPhysicalThresholdProved : Bool
round318AnyPhysicalThresholdProved = false

round318PackageAClosed : Bool
round318PackageAClosed = false

round318ClayPromotion : Bool
round318ClayPromotion = false

round318PackageAClosedIsFalse : round318PackageAClosed ≡ false
round318PackageAClosedIsFalse = refl
