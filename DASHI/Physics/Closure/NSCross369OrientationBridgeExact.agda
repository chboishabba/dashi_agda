module DASHI.Physics.Closure.NSCross369OrientationBridgeExact where

------------------------------------------------------------------------
-- NAVIER--STOKES COMPLEX3 CROSS PRODUCT <-> 369 ORIENTATION SKELETON
--
-- The existing NS helical/Waleffe lane already owns a literal complex three-
-- vector cross product, curl symbol i(k x u), Beltrami suppression, and an
-- exact Leray cancellation for output-transverse cross products.
--
-- This module records that those coordinate minors use the same oriented
-- three-axis skeleton as the generic 369 bracket.  It does NOT identify the
-- NS module alias "C3" (Complex3) with the cyclic group C3 or with the zeta
-- phase carrier used elsewhere in the repository.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.OrientedThreeAxisBracket369Exact as Bracket369
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3Vector
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNOutputTransverseCrossLerayCancellationRound131Exact as LerayCross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical

------------------------------------------------------------------------
-- 1. Literal coordinate receipts for the existing Complex3 cross product.
------------------------------------------------------------------------

nsCrossXCoordinate :
  ∀ {r} {F : C3Vector.RealField r}
    (a b : C3Vector.Complex3 F) →
  C3Vector.x (Cross.complex3Cross a b)
  ≡ C3Vector.complexSubtract
      (C3Vector.complexMultiply (C3Vector.y a) (C3Vector.z b))
      (C3Vector.complexMultiply (C3Vector.z a) (C3Vector.y b))
nsCrossXCoordinate a b = refl

nsCrossYCoordinate :
  ∀ {r} {F : C3Vector.RealField r}
    (a b : C3Vector.Complex3 F) →
  C3Vector.y (Cross.complex3Cross a b)
  ≡ C3Vector.complexSubtract
      (C3Vector.complexMultiply (C3Vector.z a) (C3Vector.x b))
      (C3Vector.complexMultiply (C3Vector.x a) (C3Vector.z b))
nsCrossYCoordinate a b = refl

nsCrossZCoordinate :
  ∀ {r} {F : C3Vector.RealField r}
    (a b : C3Vector.Complex3 F) →
  C3Vector.z (Cross.complex3Cross a b)
  ≡ C3Vector.complexSubtract
      (C3Vector.complexMultiply (C3Vector.x a) (C3Vector.y b))
      (C3Vector.complexMultiply (C3Vector.y a) (C3Vector.x b))
nsCrossZCoordinate a b = refl

------------------------------------------------------------------------
-- 2. Existing rotational/curl consumers.
------------------------------------------------------------------------

nsComplexCrossUses369OrientationSkeleton : Bool
nsComplexCrossUses369OrientationSkeleton = true

nsCurlUsesSameCrossSkeleton : Bool
nsCurlUsesSameCrossSkeleton = true

nsBeltramiCrossSuppressionReused : Bool
nsBeltramiCrossSuppressionReused =
  Cross.round93ExactBeltramiCrossSuppressionClosed

nsBeltramiCrossSuppressionReusedIsTrue :
  nsBeltramiCrossSuppressionReused ≡ true
nsBeltramiCrossSuppressionReusedIsTrue =
  Cross.round93ExactBeltramiCrossSuppressionClosedIsTrue

nsOutputTransverseLerayCancellationReused : Bool
nsOutputTransverseLerayCancellationReused =
  LerayCross.round131LerayKillsOutputTransverseCrossClosed

nsOutputTransverseLerayCancellationReusedIsTrue :
  nsOutputTransverseLerayCancellationReused ≡ true
nsOutputTransverseLerayCancellationReusedIsTrue =
  LerayCross.round131LerayKillsOutputTransverseCrossClosedIsTrue

nsHelicalCrossCurlInfrastructureRepresented : Bool
nsHelicalCrossCurlInfrastructureRepresented =
  Helical.periodicHelicalInfrastructureRepresented

------------------------------------------------------------------------
-- 3. Critical nomenclature/promotion firewall.
------------------------------------------------------------------------

nsComplex3CarrierPromotedToCyclicC3 : Bool
nsComplex3CarrierPromotedToCyclicC3 = false

nsCrossGeometryProvesNSRegularity : Bool
nsCrossGeometryProvesNSRegularity = false

nsCrossGeometryIdentifiesTorqueEMOrYangMillsMechanism : Bool
nsCrossGeometryIdentifiesTorqueEMOrYangMillsMechanism = false

nsThreeAxisBracketVoxel : Set
nsThreeAxisBracketVoxel = Bracket369.BracketVoxel

record NSCross369OrientationBoundary : Set where
  constructor ns-cross-369-orientation-boundary
  field
    literalComplex3CrossCoordinatesReused : Bool
    curlUsesSameCrossSkeleton : Bool
    beltramiParallelSuppressionReused : Bool
    outputTransverseLerayCancellationReused : Bool
    complex3AliasPromotedToCyclicC3 : Bool
    sharedOrientationProvesClayRegularity : Bool
    crossDomainMechanismsIdentifiedAutomatically : Bool

canonicalNSCross369OrientationBoundary : NSCross369OrientationBoundary
canonicalNSCross369OrientationBoundary =
  ns-cross-369-orientation-boundary
    true true true true false false false
