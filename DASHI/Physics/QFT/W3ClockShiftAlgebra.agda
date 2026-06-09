module DASHI.Physics.QFT.W3ClockShiftAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.DivMod using (_%_)
open import Data.Nat.Base using (NonZero; nonZero)

------------------------------------------------------------------------
-- Concrete Weyl-Heisenberg / clock-shift algebra over the finite
-- modulus already identified in the repo note.
--
-- The intended route is the 3-generator W3 algebra:
--   C^3 = I
--   S^3 = I
--   S C = ω C S
-- with ω = 7 in arithmetic modulo 19.
--
-- The implementation below is fully finite and evaluator-friendly.
-- All displayed proofs are definitional equalities that normalize to
-- refl.

modulus : Nat
modulus = 19

instance
  modulusNonZero : NonZero modulus
  modulusNonZero = nonZero

omega : Nat
omega = 7

omegaSquared : Nat
omegaSquared = 11

record Matrix3 : Set where
  constructor mkMatrix3
  field
    m11 : Nat
    m12 : Nat
    m13 : Nat
    m21 : Nat
    m22 : Nat
    m23 : Nat
    m31 : Nat
    m32 : Nat
    m33 : Nat

open Matrix3 public

zeroMatrix3 : Matrix3
zeroMatrix3 =
  mkMatrix3
    0 0 0
    0 0 0
    0 0 0

identityMatrix3 : Matrix3
identityMatrix3 =
  mkMatrix3
    1 0 0
    0 1 0
    0 0 1

clockMatrix : Matrix3
clockMatrix =
  mkMatrix3
    1 0 0
    0 omega 0
    0 0 omegaSquared

shiftMatrix : Matrix3
shiftMatrix =
  mkMatrix3
    0 1 0
    0 0 1
    1 0 0

------------------------------------------------------------------------
-- Matrix operations.

_+19_ : Nat → Nat → Nat
a +19 b = (a + b) % modulus

_⋆_ : Nat → Nat → Nat
a ⋆ b = (a * b) % modulus

matrixMul : Matrix3 → Matrix3 → Matrix3
matrixMul A B =
  mkMatrix3
    (((m11 A ⋆ m11 B) +19 (m12 A ⋆ m21 B)) +19 (m13 A ⋆ m31 B))
    (((m11 A ⋆ m12 B) +19 (m12 A ⋆ m22 B)) +19 (m13 A ⋆ m32 B))
    (((m11 A ⋆ m13 B) +19 (m12 A ⋆ m23 B)) +19 (m13 A ⋆ m33 B))
    (((m21 A ⋆ m11 B) +19 (m22 A ⋆ m21 B)) +19 (m23 A ⋆ m31 B))
    (((m21 A ⋆ m12 B) +19 (m22 A ⋆ m22 B)) +19 (m23 A ⋆ m32 B))
    (((m21 A ⋆ m13 B) +19 (m22 A ⋆ m23 B)) +19 (m23 A ⋆ m33 B))
    (((m31 A ⋆ m11 B) +19 (m32 A ⋆ m21 B)) +19 (m33 A ⋆ m31 B))
    (((m31 A ⋆ m12 B) +19 (m32 A ⋆ m22 B)) +19 (m33 A ⋆ m32 B))
    (((m31 A ⋆ m13 B) +19 (m32 A ⋆ m23 B)) +19 (m33 A ⋆ m33 B))

scalarMul : Nat → Matrix3 → Matrix3
scalarMul k A =
  mkMatrix3
    ((k * m11 A) % modulus)
    ((k * m12 A) % modulus)
    ((k * m13 A) % modulus)
    ((k * m21 A) % modulus)
    ((k * m22 A) % modulus)
    ((k * m23 A) % modulus)
    ((k * m31 A) % modulus)
    ((k * m32 A) % modulus)
    ((k * m33 A) % modulus)

------------------------------------------------------------------------
-- Concrete arithmetic witnesses.

clockCubedIsIdentity : matrixMul (matrixMul clockMatrix clockMatrix) clockMatrix ≡ identityMatrix3
clockCubedIsIdentity = refl

shiftCubedIsIdentity : matrixMul (matrixMul shiftMatrix shiftMatrix) shiftMatrix ≡ identityMatrix3
shiftCubedIsIdentity = refl

commutationRelation : matrixMul shiftMatrix clockMatrix ≡ scalarMul omega (matrixMul clockMatrix shiftMatrix)
commutationRelation = refl

------------------------------------------------------------------------
-- Pack the algebra as a concrete witness record.

record W3ClockShiftAlgebra : Set where
  field
    clock : Matrix3
    shift : Matrix3
    clock³≡I : matrixMul (matrixMul clock clock) clock ≡ identityMatrix3
    shift³≡I : matrixMul (matrixMul shift shift) shift ≡ identityMatrix3
    commutation : matrixMul shift clock ≡ scalarMul omega (matrixMul clock shift)

canonicalW3ClockShiftAlgebra : W3ClockShiftAlgebra
canonicalW3ClockShiftAlgebra =
  record
    { clock = clockMatrix
    ; shift = shiftMatrix
    ; clock³≡I = clockCubedIsIdentity
    ; shift³≡I = shiftCubedIsIdentity
    ; commutation = commutationRelation
    }
