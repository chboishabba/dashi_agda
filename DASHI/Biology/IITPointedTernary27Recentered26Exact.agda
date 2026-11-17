module DASHI.Biology.IITPointedTernary27Recentered26Exact where

------------------------------------------------------------------------
-- ARBITRARY SELECTED CUBIE = 1 ACTIVE + TRANSPORTED 26 COMPLEMENT
--
-- The canonical 1+26 theorem is origin-pointed.  The C3^3 carrier chart gives
-- an exact finite permutation that recentres any selected cubie at the C3
-- identity.  Transporting the existing NonOrigin26 along that permutation
-- yields 26 explicit complementary cubies for every selected point.
--
-- This is an algebraic carrier permutation.  It is deliberately NOT promoted
-- to an automorphism of the non-periodic {-1,0,+1} nearest-neighbour geometry,
-- outer-face incidence, or Cech gluing data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Sum.Base using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Biology.Physical.C3CubeFourier27Exact as Cube
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Biology.IITPointedTernary27FaceGluingExact as Pointed
import DASHI.Biology.IITPointedTernary27CyclotomicCellExact as Chart
import DASHI.Biology.IITPointedTernary27Origin26Exact as Origin26
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Shape26

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
cubeNeg (Cube.cube3 x y z) =
  Cube.cube3 (phaseNeg x) (phaseNeg y) (phaseNeg z)

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
  Chart.c3CubeToPoint
    (recenterCube (Chart.pointToC3Cube active) (Chart.pointToC3Cube point))

uncenterPoint :
  Geometry.Ternary27Point → Geometry.Ternary27Point → Geometry.Ternary27Point
uncenterPoint active point =
  Chart.c3CubeToPoint
    (uncenterCube (Chart.pointToC3Cube active) (Chart.pointToC3Cube point))

recenterUncenterPoint :
  (active point : Geometry.Ternary27Point) →
  recenterPoint active (uncenterPoint active point) ≡ point
recenterUncenterPoint active point
  rewrite Chart.c3PointRoundTrip
            (uncenterCube (Chart.pointToC3Cube active) (Chart.pointToC3Cube point))
        | recenterUncenterCube (Chart.pointToC3Cube active) (Chart.pointToC3Cube point)
        | Chart.pointC3RoundTrip point = refl

uncenterRecenterPoint :
  (active point : Geometry.Ternary27Point) →
  uncenterPoint active (recenterPoint active point) ≡ point
uncenterRecenterPoint active point
  rewrite Chart.c3PointRoundTrip
            (recenterCube (Chart.pointToC3Cube active) (Chart.pointToC3Cube point))
        | uncenterRecenterCube (Chart.pointToC3Cube active) (Chart.pointToC3Cube point)
        | Chart.pointC3RoundTrip point = refl

recenterSelectedCubieIsOrigin :
  (active : Geometry.Ternary27Point) →
  recenterPoint active active ≡ Geometry.origin
recenterSelectedCubieIsOrigin active
  rewrite recenterCubeSelfIsZero (Chart.pointToC3Cube active) = refl

RecenteredNonActive26 : Set
RecenteredNonActive26 = Origin26.NonActive26

recenteredNonActiveToCubie :
  Geometry.Ternary27Point → RecenteredNonActive26 → Geometry.Ternary27Point
recenteredNonActiveToCubie active q =
  uncenterPoint active (Origin26.nonActiveToCubie q)

recenteredNonActiveNeverHitsSelected :
  (active : Geometry.Ternary27Point) →
  (q : RecenteredNonActive26) →
  recenteredNonActiveToCubie active q ≡ active →
  ⊥
recenteredNonActiveNeverHitsSelected active q equality =
  Origin26.nonActiveCubieIsNotOrigin q centeredEquality
  where
  centeredEquality :
    Origin26.nonActiveToCubie q ≡ Geometry.origin
  centeredEquality =
    trans
      (sym (recenterUncenterPoint active (Origin26.nonActiveToCubie q)))
      (trans
        (cong (recenterPoint active) equality)
        (recenterSelectedCubieIsOrigin active))

inj₂Injective :
  ∀ {A B : Set} {x y : B} →
  (inj₂ x : A ⊎ B) ≡ inj₂ y →
  x ≡ y
inj₂Injective refl = refl

nonActiveToCubieInjective :
  {left right : RecenteredNonActive26} →
  Origin26.nonActiveToCubie left ≡ Origin26.nonActiveToCubie right →
  left ≡ right
nonActiveToCubieInjective {left} {right} equality =
  inj₂Injective branchEquality
  where
  branchEquality :
    (inj₂ left : Shape26.CubeAlbert27) ≡ inj₂ right
  branchEquality =
    trans
      (sym (Shape26.toAfterFrom (inj₂ left)))
      (trans
        (cong Shape26.toAlbertShape equality)
        (Shape26.toAfterFrom (inj₂ right)))

recenteredNonActiveInjective :
  (active : Geometry.Ternary27Point) →
  {left right : RecenteredNonActive26} →
  recenteredNonActiveToCubie active left
  ≡ recenteredNonActiveToCubie active right →
  left ≡ right
recenteredNonActiveInjective active {left} {right} equality =
  nonActiveToCubieInjective centeredEquality
  where
  centeredEquality :
    Origin26.nonActiveToCubie left ≡ Origin26.nonActiveToCubie right
  centeredEquality =
    trans
      (sym (recenterUncenterPoint active (Origin26.nonActiveToCubie left)))
      (trans
        (cong (recenterPoint active) equality)
        (recenterUncenterPoint active (Origin26.nonActiveToCubie right)))

record ArbitraryPointedComplement26 : Set where
  constructor arbitrary-pointed-complement26
  field
    selected : Pointed.PointedTernary27Cube
    complement : RecenteredNonActive26 → Geometry.Ternary27Point
    complementIsTransported :
      (q : RecenteredNonActive26) →
      complement q ≡ recenteredNonActiveToCubie (Pointed.activeCubie selected) q
    complementAvoidsSelected :
      (q : RecenteredNonActive26) →
      complement q ≡ Pointed.activeCubie selected → ⊥
    complementInjective :
      {left right : RecenteredNonActive26} →
      complement left ≡ complement right → left ≡ right

open ArbitraryPointedComplement26 public

canonicalArbitraryPointedComplement26 :
  (selected : Pointed.PointedTernary27Cube) → ArbitraryPointedComplement26
canonicalArbitraryPointedComplement26 selected =
  arbitrary-pointed-complement26
    selected
    (recenteredNonActiveToCubie (Pointed.activeCubie selected))
    (λ q → refl)
    (recenteredNonActiveNeverHitsSelected (Pointed.activeCubie selected))
    (recenteredNonActiveInjective (Pointed.activeCubie selected))

record Recentered26Boundary : Set where
  constructor recentered26-boundary
  field
    everySelectedCubieHasTransportedTwentySixComplement : Bool
    transportedComplementAvoidsSelectedCubie : Bool
    transportedComplementIsInjective : Bool
    recenteringIsC3CubedCarrierPermutation : Bool
    recenteringPreservesNonperiodicGridAdjacencyByDefinition : Bool
    recenteringPreservesOuterFaceIncidenceByDefinition : Bool
    transportedComplementDeterminesIITPhiByDefinition : Bool

open Recentered26Boundary public

canonicalRecentered26Boundary : Recentered26Boundary
canonicalRecentered26Boundary =
  recentered26-boundary
    true true true true
    false false false

recentringDoesNotManufactureGeometricSymmetry :
  recenteringPreservesNonperiodicGridAdjacencyByDefinition
    canonicalRecentered26Boundary ≡ false
recentringDoesNotManufactureGeometricSymmetry = refl

recentringDoesNotManufactureFaceSymmetry :
  recenteringPreservesOuterFaceIncidenceByDefinition
    canonicalRecentered26Boundary ≡ false
recentringDoesNotManufactureFaceSymmetry = refl
