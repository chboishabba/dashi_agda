module DASHI.Crypto.MLKEMNTTActualCBD2ScalarCollisionExact where

------------------------------------------------------------------------
-- ACTUAL FIPS-203 CONSTANT-NTT SCALAR COLLISION ON A CBD2 SUPPORT SLICE
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- For residue i=0, gamma=zeta=17.  The constant part of
--   f mod (X^2-gamma)
-- receives coefficient f_(2j) with multiplier gamma^j.
--
-- Three actual multiplier values are
--   gamma^0 = 1,
--   gamma^4 = 296 mod 3329,
--   gamma^6 = 2319 mod 3329.
--
-- There is a small integer relation
--   -3*1 - 1*296 + 3*2319 = 6658 = 2*3329.
-- Hence two distinct CBD2-supported triples
--   A = (-1,-1,+1)
--   B = (+2, 0,-2)
-- at source degrees 0,8,12 have exactly the same first constant NTT scalar.
--
-- This is an explicit same-object FIPS-constant collision, not a cardinality
-- heuristic.  It proves that one local NTT scalar does not uniquely determine
-- even this three-coefficient CBD2 source slice.  It is not an ML-KEM break:
-- all other NTT/public coordinates remain available to the real verifier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)
open import DASHI.Foundations.Base369Nat using (_%_)

q : Nat
q = 3329

gamma : Nat
gamma = 17

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc n) = base * pow base n

weight0 : Nat
weight0 = pow gamma 0 % q

weight4 : Nat
weight4 = pow gamma 4 % q

weight6 : Nat
weight6 = pow gamma 6 % q

weight0Is1 : weight0 ≡ 1
weight0Is1 = refl

weight4Is296 : weight4 ≡ 296
weight4Is296 = refl

weight6Is2319 : weight6 ≡ 2319
weight6Is2319 = refl

------------------------------------------------------------------------
-- Centered CBD2 coefficients represented by their canonical residues mod q.
------------------------------------------------------------------------

minus1 minus2 plus0 plus1 plus2 : Nat
minus1 = 3328
minus2 = 3327
plus0 = 0
plus1 = 1
plus2 = 2

record CBD2TripleSlice : Set where
  constructor cbd2TripleSlice
  field
    degree0 degree8 degree12 : Nat

open CBD2TripleSlice public

sourceA sourceB : CBD2TripleSlice
sourceA = cbd2TripleSlice minus1 minus1 plus1
sourceB = cbd2TripleSlice plus2 plus0 minus2

firstConstantNTTScalar : CBD2TripleSlice → Nat
firstConstantNTTScalar source =
  ( degree0 source * weight0
  + degree8 source * weight4
  + degree12 source * weight6
  ) % q

sourceAImageIs2022 : firstConstantNTTScalar sourceA ≡ 2022
sourceAImageIs2022 = refl

sourceBImageIs2022 : firstConstantNTTScalar sourceB ≡ 2022
sourceBImageIs2022 = refl

actualCBD2SliceScalarCollision :
  firstConstantNTTScalar sourceA ≡ firstConstantNTTScalar sourceB
actualCBD2SliceScalarCollision = refl

sourceAandBAreDistinct : sourceA ≡ sourceB → ⊥
sourceAandBAreDistinct equality = impossible (cong degree0 equality)
  where
  impossible : 3328 ≡ 2 → ⊥
  impossible ()

record ActualScalarCollision : Set where
  constructor actualScalarCollision
  field
    left right : CBD2TripleSlice
    distinct : left ≡ right → ⊥
    sameScalar : firstConstantNTTScalar left ≡ firstConstantNTTScalar right

open ActualScalarCollision public

fipsCBD2FirstScalarCollision : ActualScalarCollision
fipsCBD2FirstScalarCollision =
  actualScalarCollision sourceA sourceB sourceAandBAreDistinct actualCBD2SliceScalarCollision

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record ScalarCollisionBoundary : Set where
  constructor scalarCollisionBoundary
  field
    oneScalarUniquelyDeterminesCBD2SourceSlice : Set
    collisionOnlyConcernsOneObservedScalar : Set

open ScalarCollisionBoundary public

scalarCollisionBoundaryWitness : ScalarCollisionBoundary
scalarCollisionBoundaryWitness =
  scalarCollisionBoundary
    (sourceA ≡ sourceB → ⊥)
    (firstConstantNTTScalar sourceA ≡ firstConstantNTTScalar sourceB)
