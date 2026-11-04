module DASHI.Moonshine.Base369AlbertF3CubeHamiltonianSymmetryMaxCutExact where

-- Canonical prior owners (do not recreate their cubes or spectra):
-- geometry: literal balanced 3x3x3, P3^3 nonperiodic adjacency.
-- scalar+26: existing origin/NonOrigin26 Albert SHAPE codec.
-- periodic: C3^3 torus has wraparound, not the literal cube graph.
-- spectral: native character / adjacency separation.
--
-- EXTERNAL source: Robert L. Griess Jr., J. Algebra 131 (1990),
-- DOI 10.1016/0021-8693(90)90176-O.
-- The *actual 27-dimensional Albert Jordan algebra* admits A=3^3
-- with twenty-seven one-dimensional A-character spaces and normalizer
-- SL(3,3). This is NOT the 196884-dimensional Monster Griess algebra.
-- A=(Z/3)^3 is NOT the cyclic order-27 Monster subgroup.
--
-- This module proves the generic SAME-ALGEBRA Hamiltonian
-- stabilizer theorem and exactly references the existing cube owners.
-- A concrete 27x27 Jordan multiplication and SL3 eigenspace spectral
-- calculations are separately executed in local exact Python.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Setω)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Shape
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Albert
import DASHI.Moonshine.Base369Ternary27CharacterAdjacencyEquivarianceExact as Char
import DASHI.Moonshine.Base369Ternary27PathCubeSpectralBandsExact as Path
import DASHI.Moonshine.Base369PeriodicTernaryTorusPathRestrictionBidiExact as Torus
import DASHI.Moonshine.Base369PeriodicHeisenbergFibreEquivarianceExact as Periodic

-- Earlier **set-level** bijection is retained as a statement about the
-- *geometric origin*, not an identification with the algebraic unit vector.
oldOriginIsTheScalarShape :
  Shape.toAlbertShape Cube.origin ≡ inj₁ Albert.scalarLine
oldOriginIsTheScalarShape = Shape.originMapsToScalar

-- Coordinate translation on the periodic group (Z/3)^3 has order 3.
-- It never generates a cyclic order-27 carrier.
translateX : Cube.Ternary27Point → Cube.Ternary27Point
translateX (Cube.ternary27Point x y z) =
  Cube.ternary27Point (Periodic.cyclicIncrement x) y z

translateXOrderThree :
  (p : Cube.Ternary27Point) →
  translateX (translateX (translateX p)) ≡ p
translateXOrderThree (Cube.ternary27Point SSP.sspNegOne y z) = refl
translateXOrderThree (Cube.ternary27Point SSP.sspZero y z) = refl
translateXOrderThree (Cube.ternary27Point SSP.sspPosOne y z) = refl

translateXNotIdentity :
  translateX Cube.origin ≡ Cube.origin → ⊥
translateXNotIdentity ()

-- A direct non-wrapping graph vs periodic group distinction already
-- owned by the earlier periodic-to-path restriction theorem:
periodicWrapNotNativeGrid :
  Cube.HypervoxelAdjacent
    (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero)
    (Cube.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero)
  → ⊥
periodicWrapNotNativeGrid (Cube.adjacentX ())

-- This is the HIGH-VALUE actual-Jordan-algebra Hamiltonian gate:
-- If the multiplication operator L_h(x)=h∘x commutes with EVERY
-- element of a symmetry A, then h must itself be A-fixed, because
-- L_h(unit)=h. It does NOT require associativity of the Jordan product.
record SourceJordanHamiltonian (Actor : Set) : Setω where
  field
    J : Set
    unit : J
    _∘_ : J → J → J
    act : Actor → J → J
    rightUnit : (x : J) → (x ∘ unit) ≡ x
    unitFixed : (a : Actor) → act a unit ≡ unit
open SourceJordanHamiltonian public

leftMultiplication :
  ∀ {Actor : Set} (S : SourceJordanHamiltonian Actor) →
  J S → J S → J S
leftMultiplication S h x = _∘_ S h x

record HamiltonianCommutesWithAction
  {Actor : Set} (S : SourceJordanHamiltonian Actor)
  (h : J S) : Set where
  field
    commuting :
      (a : Actor) (x : J S) →
      act S a (leftMultiplication S h x)
      ≡ leftMultiplication S h (act S a x)
open HamiltonianCommutesWithAction public

commutingJordanHamiltonianForcesFixedGenerator :
  ∀ {Actor : Set} (S : SourceJordanHamiltonian Actor)
  (h : J S) (C : HamiltonianCommutesWithAction S h)
  (a : Actor) →
  act S a h ≡ h
commutingJordanHamiltonianForcesFixedGenerator S h C a =
  trans
    (cong (act S a) (sym (rightUnit S h)))
    (trans
      (commuting C a (unit S))
      (trans
        (cong (λ x → _∘_ S h x) (unitFixed S a))
        (rightUnit S h)))

-- In the source's 27=1+26 Albert fine grading, A fixes only
-- its trivial-character line. Once an ACTUAL Albert realization
-- supplies that same-object fact, any A-invariant L_h can therefore
-- have generator h only in the scalar line. This is not a Monster
-- spectral/KK physical receipt; it rules out promoting nontrivial
-- Albert left-multiplication to full A-symmetric Hamiltonian.
record OnlyTrivialAlbertCharacterFixed
    {Actor : Set} (S : SourceJordanHamiltonian Actor) : Setω where
  field
    ScalarLine : J S → Set
    fixedIsScalar :
      (h : J S) →
      ((a : Actor) → act S a h ≡ h) →
      ScalarLine h
open OnlyTrivialAlbertCharacterFixed public

fullAInvariantHamiltonianMustBeScalar :
  ∀ {Actor : Set} (S : SourceJordanHamiltonian Actor)
    (F : OnlyTrivialAlbertCharacterFixed S)
    (h : J S) →
    HamiltonianCommutesWithAction S h →
    ScalarLine F h
fullAInvariantHamiltonianMustBeScalar S F h C =
  fixedIsScalar F h
    (commutingJordanHamiltonianForcesFixedGenerator S h C)

-- Distinct consumers:
--  1) literal octonionic J3(O) and source 3^3 fine grading (extra witness),
--  2) actual 3x3x3 geometric nearest-neighbour Hamiltonian,
--  3) Monster VOA weight-two (196884) Griess mode multiplication.
-- No mutual identification or physical gauge/gravity solution is made.
