module DASHI.Biology.Physical.C3CubeFourier27Exact where

------------------------------------------------------------------------
-- Exact finite C3^3 / 27-cell spectral skeleton.
--
-- The state carrier and character-index carrier are both triples of C3 phases.
-- This is the finite group-theoretic content behind the 27-cell / 27-character
-- statement.  No analytic Fourier inversion over complex numbers is claimed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.GrokkingTaskCharacterPhaseExact as C3
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

Phase : Set
Phase = Wheel.DepthWheelPhase

add : Phase → Phase → Phase
add = C3.phaseComposeC3

scalarCharacter : Phase → Phase → Phase
scalarCharacter Wheel.phase-0 x = Wheel.phase-0
scalarCharacter Wheel.phase-1 x = x
scalarCharacter Wheel.phase-2 x = add x x

scalarCharacterHomomorphism :
  (k x y : Phase) →
  scalarCharacter k (add x y)
  ≡ add (scalarCharacter k x) (scalarCharacter k y)
scalarCharacterHomomorphism Wheel.phase-0 Wheel.phase-0 Wheel.phase-0 = refl
scalarCharacterHomomorphism Wheel.phase-0 Wheel.phase-0 Wheel.phase-1 = refl
scalarCharacterHomomorphism Wheel.phase-0 Wheel.phase-0 Wheel.phase-2 = refl
scalarCharacterHomomorphism Wheel.phase-0 Wheel.phase-1 Wheel.phase-0 = refl
scalarCharacterHomomorphism Wheel.phase-0 Wheel.phase-1 Wheel.phase-1 = refl
scalarCharacterHomomorphism Wheel.phase-0 Wheel.phase-1 Wheel.phase-2 = refl
scalarCharacterHomomorphism Wheel.phase-0 Wheel.phase-2 Wheel.phase-0 = refl
scalarCharacterHomomorphism Wheel.phase-0 Wheel.phase-2 Wheel.phase-1 = refl
scalarCharacterHomomorphism Wheel.phase-0 Wheel.phase-2 Wheel.phase-2 = refl
scalarCharacterHomomorphism Wheel.phase-1 Wheel.phase-0 Wheel.phase-0 = refl
scalarCharacterHomomorphism Wheel.phase-1 Wheel.phase-0 Wheel.phase-1 = refl
scalarCharacterHomomorphism Wheel.phase-1 Wheel.phase-0 Wheel.phase-2 = refl
scalarCharacterHomomorphism Wheel.phase-1 Wheel.phase-1 Wheel.phase-0 = refl
scalarCharacterHomomorphism Wheel.phase-1 Wheel.phase-1 Wheel.phase-1 = refl
scalarCharacterHomomorphism Wheel.phase-1 Wheel.phase-1 Wheel.phase-2 = refl
scalarCharacterHomomorphism Wheel.phase-1 Wheel.phase-2 Wheel.phase-0 = refl
scalarCharacterHomomorphism Wheel.phase-1 Wheel.phase-2 Wheel.phase-1 = refl
scalarCharacterHomomorphism Wheel.phase-1 Wheel.phase-2 Wheel.phase-2 = refl
scalarCharacterHomomorphism Wheel.phase-2 Wheel.phase-0 Wheel.phase-0 = refl
scalarCharacterHomomorphism Wheel.phase-2 Wheel.phase-0 Wheel.phase-1 = refl
scalarCharacterHomomorphism Wheel.phase-2 Wheel.phase-0 Wheel.phase-2 = refl
scalarCharacterHomomorphism Wheel.phase-2 Wheel.phase-1 Wheel.phase-0 = refl
scalarCharacterHomomorphism Wheel.phase-2 Wheel.phase-1 Wheel.phase-1 = refl
scalarCharacterHomomorphism Wheel.phase-2 Wheel.phase-1 Wheel.phase-2 = refl
scalarCharacterHomomorphism Wheel.phase-2 Wheel.phase-2 Wheel.phase-0 = refl
scalarCharacterHomomorphism Wheel.phase-2 Wheel.phase-2 Wheel.phase-1 = refl
scalarCharacterHomomorphism Wheel.phase-2 Wheel.phase-2 Wheel.phase-2 = refl

record Cube3 : Set where
  constructor cube3
  field
    x y z : Phase

open Cube3 public

cubeAdd : Cube3 → Cube3 → Cube3
cubeAdd (cube3 a b c) (cube3 d e f) =
  cube3 (add a d) (add b e) (add c f)

CharacterIndex : Set
CharacterIndex = Cube3

character : CharacterIndex → Cube3 → Cube3
character (cube3 ka kb kc) (cube3 a b c) =
  cube3
    (scalarCharacter ka a)
    (scalarCharacter kb b)
    (scalarCharacter kc c)

cubeCharacterHomomorphism :
  (k left right : Cube3) →
  character k (cubeAdd left right)
  ≡ cubeAdd (character k left) (character k right)
cubeCharacterHomomorphism
  (cube3 ka kb kc) (cube3 a b c) (cube3 d e f)
  rewrite scalarCharacterHomomorphism ka a d
        | scalarCharacterHomomorphism kb b e
        | scalarCharacterHomomorphism kc c f = refl

------------------------------------------------------------------------
-- Explicit 27-cell carrier and exact triple equivalence.
------------------------------------------------------------------------

data CubeCell27 : Set where
  c000 c001 c002 c010 c011 c012 c020 c021 c022 : CubeCell27
  c100 c101 c102 c110 c111 c112 c120 c121 c122 : CubeCell27
  c200 c201 c202 c210 c211 c212 c220 c221 c222 : CubeCell27

cellToCube : CubeCell27 → Cube3
cellToCube c000 = cube3 Wheel.phase-0 Wheel.phase-0 Wheel.phase-0
cellToCube c001 = cube3 Wheel.phase-0 Wheel.phase-0 Wheel.phase-1
cellToCube c002 = cube3 Wheel.phase-0 Wheel.phase-0 Wheel.phase-2
cellToCube c010 = cube3 Wheel.phase-0 Wheel.phase-1 Wheel.phase-0
cellToCube c011 = cube3 Wheel.phase-0 Wheel.phase-1 Wheel.phase-1
cellToCube c012 = cube3 Wheel.phase-0 Wheel.phase-1 Wheel.phase-2
cellToCube c020 = cube3 Wheel.phase-0 Wheel.phase-2 Wheel.phase-0
cellToCube c021 = cube3 Wheel.phase-0 Wheel.phase-2 Wheel.phase-1
cellToCube c022 = cube3 Wheel.phase-0 Wheel.phase-2 Wheel.phase-2
cellToCube c100 = cube3 Wheel.phase-1 Wheel.phase-0 Wheel.phase-0
cellToCube c101 = cube3 Wheel.phase-1 Wheel.phase-0 Wheel.phase-1
cellToCube c102 = cube3 Wheel.phase-1 Wheel.phase-0 Wheel.phase-2
cellToCube c110 = cube3 Wheel.phase-1 Wheel.phase-1 Wheel.phase-0
cellToCube c111 = cube3 Wheel.phase-1 Wheel.phase-1 Wheel.phase-1
cellToCube c112 = cube3 Wheel.phase-1 Wheel.phase-1 Wheel.phase-2
cellToCube c120 = cube3 Wheel.phase-1 Wheel.phase-2 Wheel.phase-0
cellToCube c121 = cube3 Wheel.phase-1 Wheel.phase-2 Wheel.phase-1
cellToCube c122 = cube3 Wheel.phase-1 Wheel.phase-2 Wheel.phase-2
cellToCube c200 = cube3 Wheel.phase-2 Wheel.phase-0 Wheel.phase-0
cellToCube c201 = cube3 Wheel.phase-2 Wheel.phase-0 Wheel.phase-1
cellToCube c202 = cube3 Wheel.phase-2 Wheel.phase-0 Wheel.phase-2
cellToCube c210 = cube3 Wheel.phase-2 Wheel.phase-1 Wheel.phase-0
cellToCube c211 = cube3 Wheel.phase-2 Wheel.phase-1 Wheel.phase-1
cellToCube c212 = cube3 Wheel.phase-2 Wheel.phase-1 Wheel.phase-2
cellToCube c220 = cube3 Wheel.phase-2 Wheel.phase-2 Wheel.phase-0
cellToCube c221 = cube3 Wheel.phase-2 Wheel.phase-2 Wheel.phase-1
cellToCube c222 = cube3 Wheel.phase-2 Wheel.phase-2 Wheel.phase-2

cubeToCell : Cube3 → CubeCell27
cubeToCell (cube3 Wheel.phase-0 Wheel.phase-0 Wheel.phase-0) = c000
cubeToCell (cube3 Wheel.phase-0 Wheel.phase-0 Wheel.phase-1) = c001
cubeToCell (cube3 Wheel.phase-0 Wheel.phase-0 Wheel.phase-2) = c002
cubeToCell (cube3 Wheel.phase-0 Wheel.phase-1 Wheel.phase-0) = c010
cubeToCell (cube3 Wheel.phase-0 Wheel.phase-1 Wheel.phase-1) = c011
cubeToCell (cube3 Wheel.phase-0 Wheel.phase-1 Wheel.phase-2) = c012
cubeToCell (cube3 Wheel.phase-0 Wheel.phase-2 Wheel.phase-0) = c020
cubeToCell (cube3 Wheel.phase-0 Wheel.phase-2 Wheel.phase-1) = c021
cubeToCell (cube3 Wheel.phase-0 Wheel.phase-2 Wheel.phase-2) = c022
cubeToCell (cube3 Wheel.phase-1 Wheel.phase-0 Wheel.phase-0) = c100
cubeToCell (cube3 Wheel.phase-1 Wheel.phase-0 Wheel.phase-1) = c101
cubeToCell (cube3 Wheel.phase-1 Wheel.phase-0 Wheel.phase-2) = c102
cubeToCell (cube3 Wheel.phase-1 Wheel.phase-1 Wheel.phase-0) = c110
cubeToCell (cube3 Wheel.phase-1 Wheel.phase-1 Wheel.phase-1) = c111
cubeToCell (cube3 Wheel.phase-1 Wheel.phase-1 Wheel.phase-2) = c112
cubeToCell (cube3 Wheel.phase-1 Wheel.phase-2 Wheel.phase-0) = c120
cubeToCell (cube3 Wheel.phase-1 Wheel.phase-2 Wheel.phase-1) = c121
cubeToCell (cube3 Wheel.phase-1 Wheel.phase-2 Wheel.phase-2) = c122
cubeToCell (cube3 Wheel.phase-2 Wheel.phase-0 Wheel.phase-0) = c200
cubeToCell (cube3 Wheel.phase-2 Wheel.phase-0 Wheel.phase-1) = c201
cubeToCell (cube3 Wheel.phase-2 Wheel.phase-0 Wheel.phase-2) = c202
cubeToCell (cube3 Wheel.phase-2 Wheel.phase-1 Wheel.phase-0) = c210
cubeToCell (cube3 Wheel.phase-2 Wheel.phase-1 Wheel.phase-1) = c211
cubeToCell (cube3 Wheel.phase-2 Wheel.phase-1 Wheel.phase-2) = c212
cubeToCell (cube3 Wheel.phase-2 Wheel.phase-2 Wheel.phase-0) = c220
cubeToCell (cube3 Wheel.phase-2 Wheel.phase-2 Wheel.phase-1) = c221
cubeToCell (cube3 Wheel.phase-2 Wheel.phase-2 Wheel.phase-2) = c222

cubeRoundTrip : (x : Cube3) → cellToCube (cubeToCell x) ≡ x
cubeRoundTrip (cube3 Wheel.phase-0 Wheel.phase-0 Wheel.phase-0) = refl
cubeRoundTrip (cube3 Wheel.phase-0 Wheel.phase-0 Wheel.phase-1) = refl
cubeRoundTrip (cube3 Wheel.phase-0 Wheel.phase-0 Wheel.phase-2) = refl
cubeRoundTrip (cube3 Wheel.phase-0 Wheel.phase-1 Wheel.phase-0) = refl
cubeRoundTrip (cube3 Wheel.phase-0 Wheel.phase-1 Wheel.phase-1) = refl
cubeRoundTrip (cube3 Wheel.phase-0 Wheel.phase-1 Wheel.phase-2) = refl
cubeRoundTrip (cube3 Wheel.phase-0 Wheel.phase-2 Wheel.phase-0) = refl
cubeRoundTrip (cube3 Wheel.phase-0 Wheel.phase-2 Wheel.phase-1) = refl
cubeRoundTrip (cube3 Wheel.phase-0 Wheel.phase-2 Wheel.phase-2) = refl
cubeRoundTrip (cube3 Wheel.phase-1 Wheel.phase-0 Wheel.phase-0) = refl
cubeRoundTrip (cube3 Wheel.phase-1 Wheel.phase-0 Wheel.phase-1) = refl
cubeRoundTrip (cube3 Wheel.phase-1 Wheel.phase-0 Wheel.phase-2) = refl
cubeRoundTrip (cube3 Wheel.phase-1 Wheel.phase-1 Wheel.phase-0) = refl
cubeRoundTrip (cube3 Wheel.phase-1 Wheel.phase-1 Wheel.phase-1) = refl
cubeRoundTrip (cube3 Wheel.phase-1 Wheel.phase-1 Wheel.phase-2) = refl
cubeRoundTrip (cube3 Wheel.phase-1 Wheel.phase-2 Wheel.phase-0) = refl
cubeRoundTrip (cube3 Wheel.phase-1 Wheel.phase-2 Wheel.phase-1) = refl
cubeRoundTrip (cube3 Wheel.phase-1 Wheel.phase-2 Wheel.phase-2) = refl
cubeRoundTrip (cube3 Wheel.phase-2 Wheel.phase-0 Wheel.phase-0) = refl
cubeRoundTrip (cube3 Wheel.phase-2 Wheel.phase-0 Wheel.phase-1) = refl
cubeRoundTrip (cube3 Wheel.phase-2 Wheel.phase-0 Wheel.phase-2) = refl
cubeRoundTrip (cube3 Wheel.phase-2 Wheel.phase-1 Wheel.phase-0) = refl
cubeRoundTrip (cube3 Wheel.phase-2 Wheel.phase-1 Wheel.phase-1) = refl
cubeRoundTrip (cube3 Wheel.phase-2 Wheel.phase-1 Wheel.phase-2) = refl
cubeRoundTrip (cube3 Wheel.phase-2 Wheel.phase-2 Wheel.phase-0) = refl
cubeRoundTrip (cube3 Wheel.phase-2 Wheel.phase-2 Wheel.phase-1) = refl
cubeRoundTrip (cube3 Wheel.phase-2 Wheel.phase-2 Wheel.phase-2) = refl

cellRoundTrip : (c : CubeCell27) → cubeToCell (cellToCube c) ≡ c
cellRoundTrip c000 = refl
cellRoundTrip c001 = refl
cellRoundTrip c002 = refl
cellRoundTrip c010 = refl
cellRoundTrip c011 = refl
cellRoundTrip c012 = refl
cellRoundTrip c020 = refl
cellRoundTrip c021 = refl
cellRoundTrip c022 = refl
cellRoundTrip c100 = refl
cellRoundTrip c101 = refl
cellRoundTrip c102 = refl
cellRoundTrip c110 = refl
cellRoundTrip c111 = refl
cellRoundTrip c112 = refl
cellRoundTrip c120 = refl
cellRoundTrip c121 = refl
cellRoundTrip c122 = refl
cellRoundTrip c200 = refl
cellRoundTrip c201 = refl
cellRoundTrip c202 = refl
cellRoundTrip c210 = refl
cellRoundTrip c211 = refl
cellRoundTrip c212 = refl
cellRoundTrip c220 = refl
cellRoundTrip c221 = refl
cellRoundTrip c222 = refl

-- Because CharacterIndex = Cube3 and Cube3 is exactly equivalent to CubeCell27,
-- the same 27-cell carrier indexes the finite product characters.
