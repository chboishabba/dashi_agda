module DASHI.Biology.QuasiperiodicInternalSpaceBoundaryExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)
open import DASHI.Biology.TriadicKernelLiftQuotientExact

------------------------------------------------------------------------
-- Finite cut-and-project analogue.  Physical projection and internal-window
-- selection are separate maps.  Added triadic sheets refine an internal code;
-- they do not by themselves prove irrational projection or quasiperiodicity.

data PhysicalSite : Set where
  physical0 : PhysicalSite
  physical1 : PhysicalSite
  physical2 : PhysicalSite
  physical3 : PhysicalSite
  physical4 : PhysicalSite

record SuperspacePoint : Set where
  constructor superspacePoint
  field
    physicalCoordinate : PhysicalSite
    internalCoordinate : NineSheet

open SuperspacePoint public

acceptedInternal : NineSheet → Bool
acceptedInternal (zeroTrit , zeroTrit) = true
acceptedInternal (positiveTrit , zeroTrit) = true
acceptedInternal (negativeTrit , zeroTrit) = true
acceptedInternal (zeroTrit , positiveTrit) = true
acceptedInternal (zeroTrit , negativeTrit) = true
acceptedInternal _ = false

projectPhysical : SuperspacePoint → PhysicalSite
projectPhysical = physicalCoordinate

acceptedPoint : SuperspacePoint → Bool
acceptedPoint point = acceptedInternal (internalCoordinate point)

superspacePointA : SuperspacePoint
superspacePointA = superspacePoint physical2 (positiveTrit , zeroTrit)

superspacePointB : SuperspacePoint
superspacePointB = superspacePoint physical2 (zeroTrit , positiveTrit)

samePhysicalProjectionDifferentInternalCodes :
  projectPhysical superspacePointA ≡ projectPhysical superspacePointB
samePhysicalProjectionDifferentInternalCodes = refl

bothCanonicalPointsAccepted :
  acceptedPoint superspacePointA ≡ true
  ×
  acceptedPoint superspacePointB ≡ true
bothCanonicalPointsAccepted = refl , refl

------------------------------------------------------------------------
-- Refining an internal code by one nine-sheet uses the exact product lift.

baseInternalKernel : Kernel 2
baseInternalKernel = positiveTrit vcons zeroTrit vcons vnil

refinedInternalKernel : Kernel 4
refinedInternalKernel =
  liftNine baseInternalKernel (negativeTrit , positiveTrit)

refinedInternalKernelSplitsExactly :
  splitNine refinedInternalKernel
  ≡
  (baseInternalKernel , (negativeTrit , positiveTrit))
refinedInternalKernelSplitsExactly = refl

------------------------------------------------------------------------
-- Crystallographic and quasiperiodic rotation labels are different carriers.
-- The absence of a constructor is the type-level restriction used here.

data PeriodicPlanarRotationOrder : Set where
  periodicOrder1 : PeriodicPlanarRotationOrder
  periodicOrder2 : PeriodicPlanarRotationOrder
  periodicOrder3 : PeriodicPlanarRotationOrder
  periodicOrder4 : PeriodicPlanarRotationOrder
  periodicOrder6 : PeriodicPlanarRotationOrder

data QuasiperiodicRotationOrder : Set where
  quasiOrder5 : QuasiperiodicRotationOrder
  quasiOrder8 : QuasiperiodicRotationOrder
  quasiOrder10 : QuasiperiodicRotationOrder
  quasiOrder12 : QuasiperiodicRotationOrder

record QuasiperiodicInternalSpaceBoundary : Set where
  constructor quasiperiodicInternalSpaceBoundary
  field
    nineLiftAloneSuppliesIrrationalProjection : Bool
    nineLiftAloneSuppliesIrrationalProjectionIsFalse :
      nineLiftAloneSuppliesIrrationalProjection ≡ false

    physicalProjectionRecoversInternalCoordinate : Bool
    physicalProjectionRecoversInternalCoordinateIsFalse :
      physicalProjectionRecoversInternalCoordinate ≡ false

    forbiddenPeriodicRotationIsAutomaticallyQuasiperiodic : Bool
    forbiddenPeriodicRotationIsAutomaticallyQuasiperiodicIsFalse :
      forbiddenPeriodicRotationIsAutomaticallyQuasiperiodic ≡ false

open QuasiperiodicInternalSpaceBoundary public

canonicalQuasiperiodicInternalSpaceBoundary :
  QuasiperiodicInternalSpaceBoundary
canonicalQuasiperiodicInternalSpaceBoundary =
  quasiperiodicInternalSpaceBoundary false refl false refl false refl
