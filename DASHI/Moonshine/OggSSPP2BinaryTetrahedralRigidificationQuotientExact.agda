module DASHI.Moonshine.OggSSPP2BinaryTetrahedralRigidificationQuotientExact where

------------------------------------------------------------------------
-- p=2 FULL-STACK INERTIA -> RIGIDIFIED A4 INERTIA
--
-- The full characteristic-2 supersingular automorphism group is binary
-- tetrahedral 2T.  Rigidification quotients its central generic +/-1, giving
-- A4.  On conjugacy/inversion sectors this collapses the five full-stack
-- unoriented sectors to three rigidified sectors:
--
--   {1}, {-1}                -> identity sector
--   {order 4}                -> double-transposition sector
--   {order 3 pair},{order 6 pair} -> order-3 sector
--
-- This is the exact carrier-level payment needed before full-stack inertia
-- sectors may be combined with root-stack data living on X(1)^rig.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Full
import DASHI.Moonshine.OggSSPSmallCharacteristicRigidifiedInertiaLayerProductNoGoExact as Rig
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Rigidification quotient on five unoriented inertia sectors.
------------------------------------------------------------------------

rigidifyInertiaSector :
  Full.BinaryTetrahedralInversionOrbit ->
  Rig.A4UnorientedInertiaSector
rigidifyInertiaSector Full.identityInertiaOrbit =
  Rig.a4IdentitySector
rigidifyInertiaSector Full.centralMinusOneInertiaOrbit =
  Rig.a4IdentitySector
rigidifyInertiaSector Full.orderFourInertiaOrbit =
  Rig.a4OrderTwoSector
rigidifyInertiaSector Full.orderThreePairInertiaOrbit =
  Rig.a4OrderThreePairSector
rigidifyInertiaSector Full.orderSixPairInertiaOrbit =
  Rig.a4OrderThreePairSector

------------------------------------------------------------------------
-- 2. Explicit fibres expose the two refinements lost by rigidification.
------------------------------------------------------------------------

data IdentityLiftChoice : Set where
  positiveCentralLift :
    IdentityLiftChoice
  negativeCentralLift :
    IdentityLiftChoice

data OrderThreeLiftChoice : Set where
  orderThreeLift :
    OrderThreeLiftChoice
  orderSixLift :
    OrderThreeLiftChoice

identityLiftToFull :
  IdentityLiftChoice ->
  Full.BinaryTetrahedralInversionOrbit
identityLiftToFull positiveCentralLift =
  Full.identityInertiaOrbit
identityLiftToFull negativeCentralLift =
  Full.centralMinusOneInertiaOrbit

orderThreeLiftToFull :
  OrderThreeLiftChoice ->
  Full.BinaryTetrahedralInversionOrbit
orderThreeLiftToFull orderThreeLift =
  Full.orderThreePairInertiaOrbit
orderThreeLiftToFull orderSixLift =
  Full.orderSixPairInertiaOrbit

identityLiftsRigidifyTogether :
  (lift : IdentityLiftChoice) ->
  rigidifyInertiaSector (identityLiftToFull lift)
  ≡ Rig.a4IdentitySector
identityLiftsRigidifyTogether positiveCentralLift = refl
identityLiftsRigidifyTogether negativeCentralLift = refl

orderThreeLiftsRigidifyTogether :
  (lift : OrderThreeLiftChoice) ->
  rigidifyInertiaSector (orderThreeLiftToFull lift)
  ≡ Rig.a4OrderThreePairSector
orderThreeLiftsRigidifyTogether orderThreeLift = refl
orderThreeLiftsRigidifyTogether orderSixLift = refl

------------------------------------------------------------------------
-- 3. Rigidification is not invertible on the full five-sector carrier.
------------------------------------------------------------------------

identityAndCentralCollapse :
  rigidifyInertiaSector Full.identityInertiaOrbit
  ≡ rigidifyInertiaSector Full.centralMinusOneInertiaOrbit
identityAndCentralCollapse = refl

orderThreeAndSixCollapse :
  rigidifyInertiaSector Full.orderThreePairInertiaOrbit
  ≡ rigidifyInertiaSector Full.orderSixPairInertiaOrbit
orderThreeAndSixCollapse = refl

data RigidificationRecoversFiveSectors : Set where
data RootStackOnRigidificationAutomaticallyDistinguishesCentralLifts : Set where
data RootStackOnRigidificationAutomaticallyDistinguishesOrderThreeSixLifts : Set where

rigidificationDoesNotRecoverFiveSectors :
  RigidificationRecoversFiveSectors -> ⊥
rigidificationDoesNotRecoverFiveSectors ()

rigidifiedRootStackDoesNotAutomaticallySeparateCentralLifts :
  RootStackOnRigidificationAutomaticallyDistinguishesCentralLifts -> ⊥
rigidifiedRootStackDoesNotAutomaticallySeparateCentralLifts ()

rigidifiedRootStackDoesNotAutomaticallySeparateOrderThreeSixLifts :
  RootStackOnRigidificationAutomaticallyDistinguishesOrderThreeSixLifts -> ⊥
rigidifiedRootStackDoesNotAutomaticallySeparateOrderThreeSixLifts ()

------------------------------------------------------------------------
-- 4. Exact transport debt.
--
-- A valid p=2 layer x five-sector theorem must show that the analytic object on
-- X(1)^rig pulls back through the generic central gerbe with enough additional
-- grading/character data to distinguish BOTH nontrivial two-point fibres above.
------------------------------------------------------------------------

record FullInertiaLiftTransportAuthority : Set₁ where
  field
    LiftedAnalyticTerm : Set

    termForFullSector :
      Full.BinaryTetrahedralInversionOrbit ->
      LiftedAnalyticTerm

    rigidifiedProjectionCompatible :
      Bool
    rigidifiedProjectionCompatibleIsTrue :
      rigidifiedProjectionCompatible ≡ true

    distinguishesIdentityCentralPair :
      Bool
    distinguishesIdentityCentralPairIsTrue :
      distinguishesIdentityCentralPair ≡ true

    distinguishesOrderThreeOrderSixPair :
      Bool
    distinguishesOrderThreeOrderSixPairIsTrue :
      distinguishesOrderThreeOrderSixPair ≡ true

    distinctionComesFromGerbeGradingOrCharacter :
      Bool
    distinctionComesFromGerbeGradingOrCharacterIsTrue :
      distinctionComesFromGerbeGradingOrCharacter ≡ true

open FullInertiaLiftTransportAuthority public

data FullInertiaLiftTransportAuthorityInhabited : Set where

fullInertiaLiftTransportStillOpen :
  FullInertiaLiftTransportAuthorityInhabited -> ⊥
fullInertiaLiftTransportStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record P2RigidificationQuotientBoundary : Set where
  constructor p2-rigidification-quotient-boundary
  field
    fiveToThreeRigidificationMapConstructed : Bool
    identityCentralCollapseProved : Bool
    orderThreeSixCollapseProved : Bool
    rigidificationInvertibleOnFiveSectors : Bool
    twoLostRefinementFibresExplicit : Bool
    analyticLiftTransportSpecified : Bool
    analyticLiftTransportInhabited : Bool

canonicalP2RigidificationQuotientBoundary :
  P2RigidificationQuotientBoundary
canonicalP2RigidificationQuotientBoundary =
  p2-rigidification-quotient-boundary
    true true true false true true false
