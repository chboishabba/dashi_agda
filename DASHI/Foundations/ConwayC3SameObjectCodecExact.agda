module DASHI.Foundations.ConwayC3SameObjectCodecExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
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

------------------------------------------------------------------------
-- Character action from the ORIGINAL C3^3 Fourier owner: transport both
-- the character and its additive homomorphism into the same tower carrier.
------------------------------------------------------------------------

phaseAt : Cube.Cube3 → Trit → Cube.Phase
phaseAt (Cube.cube3 x y z) neg = x
phaseAt (Cube.cube3 x y z) zer = y
phaseAt (Cube.cube3 x y z) pos = z

towerCharacter :
  Cube.Cube3 → Tower.ThreeSuperThree → Tower.ThreeSuperThree
towerCharacter index f t =
  phaseToTrit
    (Cube.scalarCharacter (phaseAt index t) (tritToPhase (f t)))

cubeCharacterPreservedPointwise :
  (k c : Cube.Cube3) (t : Trit) →
  cubeToTower (Cube.character k c) t
    ≡ towerCharacter k (cubeToTower c) t
cubeCharacterPreservedPointwise
  (Cube.cube3 ka kb kc) (Cube.cube3 a b c) neg
  rewrite phaseRoundTrip a = refl
cubeCharacterPreservedPointwise
  (Cube.cube3 ka kb kc) (Cube.cube3 a b c) zer
  rewrite phaseRoundTrip b = refl
cubeCharacterPreservedPointwise
  (Cube.cube3 ka kb kc) (Cube.cube3 a b c) pos
  rewrite phaseRoundTrip c = refl

towerCharacterHomomorphism :
  (k : Cube.Cube3) (f g : Tower.ThreeSuperThree) (t : Trit) →
  towerCharacter k (towerAdd f g) t
    ≡ towerAdd (towerCharacter k f) (towerCharacter k g) t
towerCharacterHomomorphism k f g t
  rewrite phaseRoundTrip
    (Cube.add (tritToPhase (f t)) (tritToPhase (g t)))
        | phaseRoundTrip
    (Cube.scalarCharacter (phaseAt k t) (tritToPhase (f t)))
        | phaseRoundTrip
    (Cube.scalarCharacter (phaseAt k t) (tritToPhase (g t))) =
  cong phaseToTrit
    (Cube.scalarCharacterHomomorphism
      (phaseAt k t)
      (tritToPhase (f t))
      (tritToPhase (g t)))

------------------------------------------------------------------------
-- Literal bidirectional six-bit word codec. The original trit encoder
-- reserves 11, and its strict decoder rejects any reserved component.
------------------------------------------------------------------------

tripleToTower : Bits.TritTriple → Tower.ThreeSuperThree
tripleToTower (a , (b , c)) neg = a
tripleToTower (a , (b , c)) zer = b
tripleToTower (a , (b , c)) pos = c

decodeCubeBits : Bits.WordTriple → Maybe Cube.Cube3
decodeCubeBits word with Bits.decodeTriple word
... | nothing = nothing
... | just triple = just (towerToCube (tripleToTower triple))

cubeBitRoundTrip : (c : Cube.Cube3) →
  decodeCubeBits (cubeBits c) ≡ just c
cubeBitRoundTrip (Cube.cube3 a b c)
  rewrite Bits.triple-roundtrip
    (phaseToTrit a , (phaseToTrit b , phaseToTrit c))
        | phaseRoundTrip a
        | phaseRoundTrip b
        | phaseRoundTrip c = refl

reservedCubeWordRejected :
  decodeCubeBits
    (Bits.word11 , (Bits.word00 , Bits.word00)) ≡ nothing
reservedCubeWordRejected = refl
