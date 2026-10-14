module DASHI.Reasoning.Ternary27ArbitraryPointed26TransportExact where

------------------------------------------------------------------------
-- ARBITRARY-POINTED TERNARY-27 -> 1 + 26 TRANSPORT
--
-- Cross-pollination from the pointed-27 work, rewritten here over only the
-- lower-level carriers already present on this exceptional branch.
--
-- The existing same-carrier theorem is origin-pointed:
--
--   Ternary27Point <-> ScalarLine + NonOrigin26.
--
-- The exact C3^3 carrier chart gives a translation that recentres ANY selected
-- point to the geometric origin.  Conjugating the existing origin-pointed
-- bijection by this translation yields, for every selected point s,
--
--   Ternary27Point <-> ScalarLine + NonOrigin26
--
-- with s mapping to the scalar summand and the other 26 points mapping
-- injectively to the transported complement.
--
-- IMPORTANT FIREWALL:
-- This is a carrier permutation / pointed-atlas rechart.  It is not asserted to
-- preserve the non-periodic {-1,0,+1} nearest-neighbour grid, outer-face
-- incidence, Cech gluing, Jordan multiplication, or the full E6 action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Biology.Physical.C3CubeFourier27Exact as Cube
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Shape26

------------------------------------------------------------------------
-- 1. Exact signed-trit <-> C3 chart.
------------------------------------------------------------------------

signedTritToPhase : SSP.SSPTrit → Cube.Phase
signedTritToPhase SSP.sspNegOne = Wheel.phase-2
signedTritToPhase SSP.sspZero = Wheel.phase-0
signedTritToPhase SSP.sspPosOne = Wheel.phase-1

phaseToSignedTrit : Cube.Phase → SSP.SSPTrit
phaseToSignedTrit Wheel.phase-0 = SSP.sspZero
phaseToSignedTrit Wheel.phase-1 = SSP.sspPosOne
phaseToSignedTrit Wheel.phase-2 = SSP.sspNegOne

signedTritPhaseRoundTrip :
  (t : SSP.SSPTrit) → phaseToSignedTrit (signedTritToPhase t) ≡ t
signedTritPhaseRoundTrip SSP.sspNegOne = refl
signedTritPhaseRoundTrip SSP.sspZero = refl
signedTritPhaseRoundTrip SSP.sspPosOne = refl

phaseSignedTritRoundTrip :
  (p : Cube.Phase) → signedTritToPhase (phaseToSignedTrit p) ≡ p
phaseSignedTritRoundTrip Wheel.phase-0 = refl
phaseSignedTritRoundTrip Wheel.phase-1 = refl
phaseSignedTritRoundTrip Wheel.phase-2 = refl

pointToC3Cube : Geometry.Ternary27Point → Cube.Cube3
pointToC3Cube (Geometry.ternary27Point x y z) =
  Cube.cube3 (signedTritToPhase x) (signedTritToPhase y) (signedTritToPhase z)

c3CubeToPoint : Cube.Cube3 → Geometry.Ternary27Point
c3CubeToPoint (Cube.cube3 x y z) =
  Geometry.ternary27Point (phaseToSignedTrit x) (phaseToSignedTrit y) (phaseToSignedTrit z)

pointC3RoundTrip :
  (point : Geometry.Ternary27Point) → c3CubeToPoint (pointToC3Cube point) ≡ point
pointC3RoundTrip (Geometry.ternary27Point x y z)
  rewrite signedTritPhaseRoundTrip x
        | signedTritPhaseRoundTrip y
        | signedTritPhaseRoundTrip z = refl

c3PointRoundTrip :
  (cube : Cube.Cube3) → pointToC3Cube (c3CubeToPoint cube) ≡ cube
c3PointRoundTrip (Cube.cube3 x y z)
  rewrite phaseSignedTritRoundTrip x
        | phaseSignedTritRoundTrip y
        | phaseSignedTritRoundTrip z = refl

------------------------------------------------------------------------
-- 2. Exact C3^3 recentering.
------------------------------------------------------------------------

phaseNeg : Cube.Phase → Cube.Phase
phaseNeg Wheel.phase-0 = Wheel.phase-0
phaseNeg Wheel.phase-1 = Wheel.phase-2
phaseNeg Wheel.phase-2 = Wheel.phase-1

phaseNegLeft :
  (p : Cube.Phase) → Cube.add (phaseNeg p) p ≡ Wheel.phase-0
phaseNegLeft Wheel.phase-0 = refl
phaseNegLeft Wheel.phase-1 = refl
phaseNegLeft Wheel.phase-2 = refl

phaseNegRight :
  (p : Cube.Phase) → Cube.add p (phaseNeg p) ≡ Wheel.phase-0
phaseNegRight Wheel.phase-0 = refl
phaseNegRight Wheel.phase-1 = refl
phaseNegRight Wheel.phase-2 = refl

phaseRecenterRoundTrip :
  (active x : Cube.Phase) →
  Cube.add active (Cube.add (phaseNeg active) x) ≡ x
phaseRecenterRoundTrip Wheel.phase-0 Wheel.phase-0 = refl
phaseRecenterRoundTrip Wheel.phase-0 Wheel.phase-1 = refl
phaseRecenterRoundTrip Wheel.phase-0 Wheel.phase-2 = refl
phaseRecenterRoundTrip Wheel.phase-1 Wheel.phase-0 = refl
phaseRecenterRoundTrip Wheel.phase-1 Wheel.phase-1 = refl
phaseRecenterRoundTrip Wheel.phase-1 Wheel.phase-2 = refl
phaseRecenterRoundTrip Wheel.phase-2 Wheel.phase-0 = refl
phaseRecenterRoundTrip Wheel.phase-2 Wheel.phase-1 = refl
phaseRecenterRoundTrip Wheel.phase-2 Wheel.phase-2 = refl

phaseUncenterRoundTrip :
  (active x : Cube.Phase) →
  Cube.add (phaseNeg active) (Cube.add active x) ≡ x
phaseUncenterRoundTrip Wheel.phase-0 Wheel.phase-0 = refl
phaseUncenterRoundTrip Wheel.phase-0 Wheel.phase-1 = refl
phaseUncenterRoundTrip Wheel.phase-0 Wheel.phase-2 = refl
phaseUncenterRoundTrip Wheel.phase-1 Wheel.phase-0 = refl
phaseUncenterRoundTrip Wheel.phase-1 Wheel.phase-1 = refl
phaseUncenterRoundTrip Wheel.phase-1 Wheel.phase-2 = refl
phaseUncenterRoundTrip Wheel.phase-2 Wheel.phase-0 = refl
phaseUncenterRoundTrip Wheel.phase-2 Wheel.phase-1 = refl
phaseUncenterRoundTrip Wheel.phase-2 Wheel.phase-2 = refl

cubeNeg : Cube.Cube3 → Cube.Cube3
cubeNeg (Cube.cube3 x y z) = Cube.cube3 (phaseNeg x) (phaseNeg y) (phaseNeg z)

recenterCube : Cube.Cube3 → Cube.Cube3 → Cube.Cube3
recenterCube active point = Cube.cubeAdd (cubeNeg active) point

uncenterCube : Cube.Cube3 → Cube.Cube3 → Cube.Cube3
uncenterCube active point = Cube.cubeAdd active point

recenterUncenterCube :
  (active point : Cube.Cube3) →
  recenterCube active (uncenterCube active point) ≡ point
recenterUncenterCube
  (Cube.cube3 ax ay az) (Cube.cube3 x y z)
  rewrite phaseUncenterRoundTrip ax x
        | phaseUncenterRoundTrip ay y
        | phaseUncenterRoundTrip az z = refl

uncenterRecenterCube :
  (active point : Cube.Cube3) →
  uncenterCube active (recenterCube active point) ≡ point
uncenterRecenterCube
  (Cube.cube3 ax ay az) (Cube.cube3 x y z)
  rewrite phaseRecenterRoundTrip ax x
        | phaseRecenterRoundTrip ay y
        | phaseRecenterRoundTrip az z = refl

zeroCube : Cube.Cube3
zeroCube = Cube.cube3 Wheel.phase-0 Wheel.phase-0 Wheel.phase-0

recenterCubeSelfIsZero :
  (active : Cube.Cube3) → recenterCube active active ≡ zeroCube
recenterCubeSelfIsZero (Cube.cube3 x y z)
  rewrite phaseNegLeft x | phaseNegLeft y | phaseNegLeft z = refl

recenterPoint :
  Geometry.Ternary27Point → Geometry.Ternary27Point → Geometry.Ternary27Point
recenterPoint active point =
  c3CubeToPoint (recenterCube (pointToC3Cube active) (pointToC3Cube point))

uncenterPoint :
  Geometry.Ternary27Point → Geometry.Ternary27Point → Geometry.Ternary27Point
uncenterPoint active point =
  c3CubeToPoint (uncenterCube (pointToC3Cube active) (pointToC3Cube point))

recenterUncenterPoint :
  (active point : Geometry.Ternary27Point) →
  recenterPoint active (uncenterPoint active point) ≡ point
recenterUncenterPoint active point
  rewrite c3PointRoundTrip (uncenterCube (pointToC3Cube active) (pointToC3Cube point))
        | recenterUncenterCube (pointToC3Cube active) (pointToC3Cube point)
        | pointC3RoundTrip point = refl

uncenterRecenterPoint :
  (active point : Geometry.Ternary27Point) →
  uncenterPoint active (recenterPoint active point) ≡ point
uncenterRecenterPoint active point
  rewrite c3PointRoundTrip (recenterCube (pointToC3Cube active) (pointToC3Cube point))
        | uncenterRecenterCube (pointToC3Cube active) (pointToC3Cube point)
        | pointC3RoundTrip point = refl

recenterSelectedIsOrigin :
  (selected : Geometry.Ternary27Point) → recenterPoint selected selected ≡ Geometry.origin
recenterSelectedIsOrigin selected
  rewrite recenterCubeSelfIsZero (pointToC3Cube selected) = refl

------------------------------------------------------------------------
-- 3. Conjugate the existing origin-pointed 1+26 equivalence.
------------------------------------------------------------------------

toSelectedShape :
  Geometry.Ternary27Point → Geometry.Ternary27Point → Shape26.CubeAlbert27
toSelectedShape selected point = Shape26.toAlbertShape (recenterPoint selected point)

fromSelectedShape :
  Geometry.Ternary27Point → Shape26.CubeAlbert27 → Geometry.Ternary27Point
fromSelectedShape selected shape = uncenterPoint selected (Shape26.fromAlbertShape shape)

fromAfterToSelected :
  (selected point : Geometry.Ternary27Point) →
  fromSelectedShape selected (toSelectedShape selected point) ≡ point
fromAfterToSelected selected point
  rewrite Shape26.fromAfterTo (recenterPoint selected point)
        | uncenterRecenterPoint selected point = refl

toAfterFromSelected :
  (selected : Geometry.Ternary27Point) →
  (shape : Shape26.CubeAlbert27) →
  toSelectedShape selected (fromSelectedShape selected shape) ≡ shape
toAfterFromSelected selected shape
  rewrite recenterUncenterPoint selected (Shape26.fromAlbertShape shape)
        | Shape26.toAfterFrom shape = refl

selectedMapsToScalar :
  (selected : Geometry.Ternary27Point) →
  toSelectedShape selected selected ≡ inj₁ Exceptional.scalarLine
selectedMapsToScalar selected
  rewrite recenterSelectedIsOrigin selected = Shape26.originMapsToScalar

transportedComplementPoint :
  Geometry.Ternary27Point → Shape26.NonOrigin26 → Geometry.Ternary27Point
transportedComplementPoint selected q = fromSelectedShape selected (inj₂ q)

inj₂NotScalar :
  {q : Shape26.NonOrigin26} →
  (inj₂ q : Shape26.CubeAlbert27) ≡ inj₁ Exceptional.scalarLine → ⊥
inj₂NotScalar ()

transportedComplementNeverSelected :
  (selected : Geometry.Ternary27Point) →
  (q : Shape26.NonOrigin26) →
  transportedComplementPoint selected q ≡ selected → ⊥
transportedComplementNeverSelected selected q equality =
  inj₂NotScalar branchEquality
  where
  branchEquality :
    (inj₂ q : Shape26.CubeAlbert27) ≡ inj₁ Exceptional.scalarLine
  branchEquality =
    trans
      (sym (toAfterFromSelected selected (inj₂ q)))
      (trans
        (cong (toSelectedShape selected) equality)
        (selectedMapsToScalar selected))

inj₂Injective :
  ∀ {A B : Set} {x y : B} → (inj₂ x : A ⊎ B) ≡ inj₂ y → x ≡ y
inj₂Injective refl = refl

transportedComplementInjective :
  (selected : Geometry.Ternary27Point) →
  {left right : Shape26.NonOrigin26} →
  transportedComplementPoint selected left
  ≡ transportedComplementPoint selected right →
  left ≡ right
transportedComplementInjective selected {left} {right} equality =
  inj₂Injective branchEquality
  where
  branchEquality :
    (inj₂ left : Exceptional.ScalarLine ⊎ Shape26.NonOrigin26)
    ≡ inj₂ right
  branchEquality =
    trans
      (sym (toAfterFromSelected selected (inj₂ left)))
      (trans
        (cong (toSelectedShape selected) equality)
        (toAfterFromSelected selected (inj₂ right)))

record ArbitraryPointed26Boundary : Set where
  constructor arbitrary-pointed26-boundary
  field
    everySelectedPointHasExactOnePlus26 : Bool
    selectedPointMapsToScalarSummand : Bool
    transportedComplementAvoidsSelectedPoint : Bool
    transportedComplementInjective : Bool
    recenteringIsC3CubedCarrierPermutation : Bool
    recenteringPreservesNonperiodicGridAdjacencyByDefinition : Bool
    recenteringPreservesOuterFaceIncidenceByDefinition : Bool
    onePlus26IsFullE6InvariantSplitByDefinition : Bool
open ArbitraryPointed26Boundary public

canonicalBoundary : ArbitraryPointed26Boundary
canonicalBoundary =
  arbitrary-pointed26-boundary
    true true true true true
    false false false

end DASHI.Reasoning.Ternary27ArbitraryPointed26TransportExact
