module DASHI.Foundations.ConwayC3SameObjectCodecExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Core.TriadicClosureTower as Tower
import DASHI.Biology.Physical.C3CubeFourier27Exact as Cube
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Codec.VerifiedFiniteTritCoder as Bits

-- This is a definitional equality, not a cardinality coincidence.
cubeIsTowerAtFirstFunctionLevel :
  Tower.TriadicCube ≡ Tower.ThreeSuperThree
cubeIsTowerAtFirstFunctionLevel = refl

phaseToTrit : Cube.Phase → Trit
phaseToTrit Wheel.phase-0 = neg
phaseToTrit Wheel.phase-1 = zer
phaseToTrit Wheel.phase-2 = pos

tritToPhase : Trit → Cube.Phase
tritToPhase neg = Wheel.phase-0
tritToPhase zer = Wheel.phase-1
tritToPhase pos = Wheel.phase-2

phaseRoundTrip : (p : Cube.Phase) → tritToPhase (phaseToTrit p) ≡ p
phaseRoundTrip Wheel.phase-0 = refl
phaseRoundTrip Wheel.phase-1 = refl
phaseRoundTrip Wheel.phase-2 = refl

tritRoundTrip : (t : Trit) → phaseToTrit (tritToPhase t) ≡ t
tritRoundTrip neg = refl
tritRoundTrip zer = refl
tritRoundTrip pos = refl

-- A three-axis cube is a lookup table on three trit input locations.
-- The selected tower's first function-space level IS this lookup table.
cubeToTower : Cube.Cube3 → Tower.ThreeSuperThree
cubeToTower (Cube.cube3 x y z) neg = phaseToTrit x
cubeToTower (Cube.cube3 x y z) zer = phaseToTrit y
cubeToTower (Cube.cube3 x y z) pos = phaseToTrit z

towerToCube : Tower.ThreeSuperThree → Cube.Cube3
towerToCube f =
  Cube.cube3 (tritToPhase (f neg))
             (tritToPhase (f zer))
             (tritToPhase (f pos))

cubeRoundTrip :
  (c : Cube.Cube3) → towerToCube (cubeToTower c) ≡ c
cubeRoundTrip (Cube.cube3 x y z)
  rewrite phaseRoundTrip x | phaseRoundTrip y | phaseRoundTrip z = refl

towerRoundTripPointwise :
  (f : Tower.ThreeSuperThree) (t : Trit) →
  cubeToTower (towerToCube f) t ≡ f t
towerRoundTripPointwise f neg = tritRoundTrip (f neg)
towerRoundTripPointwise f zer = tritRoundTrip (f zer)
towerRoundTripPointwise f pos = tritRoundTrip (f pos)

-- Reuse the repository's actual verified 6-bit/three-trit baseline.
cubeBits : Cube.Cube3 → Bits.WordTriple
cubeBits c =
  Bits.encodeTriple
    (cubeToTower c neg ,
      (cubeToTower c zer , cubeToTower c pos))

-- Induced cyclic operation on the tower values.
addTrit : Trit → Trit → Trit
addTrit a b =
  phaseToTrit (Cube.add (tritToPhase a) (tritToPhase b))

towerAdd : Tower.ThreeSuperThree →
           Tower.ThreeSuperThree →
           Tower.ThreeSuperThree
towerAdd f g t = addTrit (f t) (g t)

phaseAddTransport : (a b : Cube.Phase) →
  phaseToTrit (Cube.add a b)
    ≡ addTrit (phaseToTrit a) (phaseToTrit b)
phaseAddTransport a b
  rewrite phaseRoundTrip a | phaseRoundTrip b = refl

cubeAdditionPreservedPointwise :
  (a b : Cube.Cube3) (t : Trit) →
  cubeToTower (Cube.cubeAdd a b) t
    ≡ towerAdd (cubeToTower a) (cubeToTower b) t
cubeAdditionPreservedPointwise
  (Cube.cube3 x y z) (Cube.cube3 u v w) neg =
    phaseAddTransport x u
cubeAdditionPreservedPointwise
  (Cube.cube3 x y z) (Cube.cube3 u v w) zer =
    phaseAddTransport y v
cubeAdditionPreservedPointwise
  (Cube.cube3 x y z) (Cube.cube3 u v w) pos =
    phaseAddTransport z w
