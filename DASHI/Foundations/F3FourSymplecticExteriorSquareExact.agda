module DASHI.Foundations.F3FourSymplecticExteriorSquareExact where

------------------------------------------------------------------------
-- F_3^4 SYMPLECTIC -> PRIMITIVE EXTERIOR-SQUARE -> FIVE-SPACE BRIDGE
--
-- DASHI CONTRIBUTION
--
-- This module formalises the typed algebraic carrier used by the local finite
-- computation.  The raw punctured four-trit carrier is deliberately kept
-- distinct from the derived oriented-Lagrangian bivector carrier.
--
-- What is paid here:
--   * a concrete F_3^4 carrier;
--   * the standard alternating pairing;
--   * the six Plucker coordinates u wedge v;
--   * the primitive relation p12 + p34 = omega(u,v), definitionally;
--   * the five-coordinate primitive projection/expansion;
--   * exact recovery of p34 for isotropic pairs;
--   * recognition interfaces requiring two-sided maps and action intertwining.
--
-- What is NOT promoted here:
--   * |T4^x|=80 does not identify raw nonzero four-trit vectors with a null cone;
--   * order 51840 does not identify groups;
--   * the full Plucker identity and 80-state enumeration remain separate
--     theorem/computational receipts until imported as inhabitants.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as F3Add
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as F3Mul

infixl 6 _+_
infixl 7 _*_

_+_ : Trit → Trit → Trit
_+_ = F3Add._+3_

_*_ : Trit → Trit → Trit
_*_ = F3Mul._*3_

-_ : Trit → Trit
-_ = F3Add.negate3

_-_ : Trit → Trit → Trit
a - b = a + (- b)

------------------------------------------------------------------------
-- 1. Four-dimensional ternary/symplectic carrier.
------------------------------------------------------------------------

record X4 : Set where
  constructor x4
  field
    x0 : Trit
    x1 : Trit
    x2 : Trit
    x3 : Trit
open X4 public

zeroX4 : X4
zeroX4 = x4 zer zer zer zer

symplectic : X4 → X4 → Trit
symplectic u v =
  ((x0 u * x1 v) - (x1 u * x0 v))
  +
  ((x2 u * x3 v) - (x3 u * x2 v))

------------------------------------------------------------------------
-- 2. Six Plucker coordinates of u wedge v.
------------------------------------------------------------------------

det2 : Trit → Trit → Trit → Trit → Trit
det2 a b c d = (a * d) - (b * c)

record Bivector6 : Set where
  constructor bivector6
  field
    p12 : Trit
    p13 : Trit
    p14 : Trit
    p23 : Trit
    p24 : Trit
    p34 : Trit
open Bivector6 public

wedge : X4 → X4 → Bivector6
wedge u v =
  bivector6
    (det2 (x0 u) (x1 u) (x0 v) (x1 v))
    (det2 (x0 u) (x2 u) (x0 v) (x2 v))
    (det2 (x0 u) (x3 u) (x0 v) (x3 v))
    (det2 (x1 u) (x2 u) (x1 v) (x2 v))
    (det2 (x1 u) (x3 u) (x1 v) (x3 v))
    (det2 (x2 u) (x3 u) (x2 v) (x3 v))

primitiveRelation : Bivector6 → Trit
primitiveRelation p = p12 p + p34 p

primitiveRelationWedge : (u v : X4) →
  primitiveRelation (wedge u v) ≡ symplectic u v
primitiveRelationWedge u v = refl

isotropicWedgeIsPrimitive :
  (u v : X4) →
  symplectic u v ≡ zer →
  primitiveRelation (wedge u v) ≡ zer
isotropicWedgeIsPrimitive u v isotropic =
  isotropic

------------------------------------------------------------------------
-- 3. Primitive five-coordinate carrier.
------------------------------------------------------------------------

record Primitive5 : Set where
  constructor primitive5
  field
    q12 : Trit
    q13 : Trit
    q14 : Trit
    q23 : Trit
    q24 : Trit
open Primitive5 public

primitiveProjection : Bivector6 → Primitive5
primitiveProjection p = primitive5 (p12 p) (p13 p) (p14 p) (p23 p) (p24 p)

primitiveExpand : Primitive5 → Bivector6
primitiveExpand q =
  bivector6
    (q12 q)
    (q13 q)
    (q14 q)
    (q23 q)
    (q24 q)
    (- q12 q)

primitiveProjectionAfterExpand : (q : Primitive5) →
  primitiveProjection (primitiveExpand q) ≡ q
primitiveProjectionAfterExpand (primitive5 a b c d e) = refl

sumZeroRightIsNeg :
  (a b : Trit) → a + b ≡ zer → b ≡ - a
sumZeroRightIsNeg neg neg ()
sumZeroRightIsNeg neg zer ()
sumZeroRightIsNeg neg pos proof = refl
sumZeroRightIsNeg zer neg ()
sumZeroRightIsNeg zer zer proof = refl
sumZeroRightIsNeg zer pos ()
sumZeroRightIsNeg pos neg proof = refl
sumZeroRightIsNeg pos zer ()
sumZeroRightIsNeg pos pos ()

isotropicWedgeP34Recovered :
  (u v : X4) →
  symplectic u v ≡ zer →
  p34 (wedge u v) ≡ - p12 (wedge u v)
isotropicWedgeP34Recovered u v isotropic =
  sumZeroRightIsNeg
    (p12 (wedge u v))
    (p34 (wedge u v))
    isotropic

------------------------------------------------------------------------
-- 4. Plucker/null relation.
------------------------------------------------------------------------

-- In primitive coordinates this is the parabolic quadratic relation
--   -q12^2 - q13*q24 + q14*q23 = 0.
-- It is kept in native F_3 arithmetic so a later diagonalising isometry is a
-- separate recognition datum rather than silently declared canonical.
primitiveQuadratic : Primitive5 → Trit
primitiveQuadratic q =
  (- ((q12 q) * (q12 q)))
  +
  ((- ((q13 q) * (q24 q))) + ((q14 q) * (q23 q)))

pluckerRelation : Bivector6 → Trit
pluckerRelation p =
  ((p12 p) * (p34 p))
  +
  ((- ((p13 p) * (p24 p))) + ((p14 p) * (p23 p)))

primitiveQuadraticIsExpandedPlucker : (q : Primitive5) →
  primitiveQuadratic q ≡ pluckerRelation (primitiveExpand q)
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg neg neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg neg neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg neg neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg neg zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg neg zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg neg zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg neg pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg neg pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg neg pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg zer neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg zer neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg zer neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg zer zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg zer zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg zer zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg zer pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg zer pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg zer pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg pos neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg pos neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg pos neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg pos zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg pos zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg pos zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg pos pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg pos pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg neg pos pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer neg neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer neg neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer neg neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer neg zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer neg zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer neg zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer neg pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer neg pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer neg pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer zer neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer zer neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer zer neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer zer zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer zer zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer zer zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer zer pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer zer pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer zer pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer pos neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer pos neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer pos neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer pos zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer pos zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer pos zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer pos pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer pos pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg zer pos pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos neg neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos neg neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos neg neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos neg zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos neg zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos neg zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos neg pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos neg pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos neg pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos zer neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos zer neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos zer neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos zer zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos zer zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos zer zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos zer pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos zer pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos zer pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos pos neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos pos neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos pos neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos pos zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos pos zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos pos zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos pos pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos pos pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 neg pos pos pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg neg neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg neg neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg neg neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg neg zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg neg zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg neg zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg neg pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg neg pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg neg pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg zer neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg zer neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg zer neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg zer zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg zer zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg zer zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg zer pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg zer pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg zer pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg pos neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg pos neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg pos neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg pos zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg pos zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg pos zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg pos pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg pos pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer neg pos pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer neg neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer neg neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer neg neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer neg zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer neg zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer neg zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer neg pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer neg pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer neg pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer zer neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer zer neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer zer neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer zer zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer zer zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer zer zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer zer pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer zer pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer zer pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer pos neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer pos neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer pos neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer pos zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer pos zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer pos zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer pos pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer pos pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer zer pos pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos neg neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos neg neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos neg neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos neg zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos neg zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos neg zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos neg pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos neg pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos neg pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos zer neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos zer neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos zer neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos zer zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos zer zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos zer zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos zer pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos zer pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos zer pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos pos neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos pos neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos pos neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos pos zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos pos zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos pos zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos pos pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos pos pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 zer pos pos pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg neg neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg neg neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg neg neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg neg zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg neg zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg neg zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg neg pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg neg pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg neg pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg zer neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg zer neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg zer neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg zer zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg zer zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg zer zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg zer pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg zer pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg zer pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg pos neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg pos neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg pos neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg pos zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg pos zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg pos zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg pos pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg pos pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos neg pos pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer neg neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer neg neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer neg neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer neg zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer neg zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer neg zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer neg pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer neg pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer neg pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer zer neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer zer neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer zer neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer zer zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer zer zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer zer zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer zer pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer zer pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer zer pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer pos neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer pos neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer pos neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer pos zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer pos zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer pos zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer pos pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer pos pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos zer pos pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos neg neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos neg neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos neg neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos neg zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos neg zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos neg zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos neg pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos neg pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos neg pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos zer neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos zer neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos zer neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos zer zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos zer zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos zer zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos zer pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos zer pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos zer pos pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos pos neg neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos pos neg zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos pos neg pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos pos zer neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos pos zer zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos pos zer pos) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos pos pos neg) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos pos pos zer) = refl
primitiveQuadraticIsExpandedPlucker (primitive5 pos pos pos pos pos) = refl

------------------------------------------------------------------------
-- 5. Typed nonzero/decomposable/lagrangian witnesses.
------------------------------------------------------------------------

data NonZeroTrit : Trit → Set where
  negNonZero : NonZeroTrit neg
  posNonZero : NonZeroTrit pos

data NonZeroBivector : Bivector6 → Set where
  nonzero12 : {p : Bivector6} → NonZeroTrit (p12 p) → NonZeroBivector p
  nonzero13 : {p : Bivector6} → NonZeroTrit (p13 p) → NonZeroBivector p
  nonzero14 : {p : Bivector6} → NonZeroTrit (p14 p) → NonZeroBivector p
  nonzero23 : {p : Bivector6} → NonZeroTrit (p23 p) → NonZeroBivector p
  nonzero24 : {p : Bivector6} → NonZeroTrit (p24 p) → NonZeroBivector p
  nonzero34 : {p : Bivector6} → NonZeroTrit (p34 p) → NonZeroBivector p

record OrientedLagrangianBivector : Set where
  constructor oriented-lagrangian-bivector
  field
    bivector : Bivector6
    primitive : primitiveRelation bivector ≡ zer
    decomposable : pluckerRelation bivector ≡ zer
    nonzero : NonZeroBivector bivector
open OrientedLagrangianBivector public

record PluckerClosureReceipt : Set where
  field
    wedgeIsDecomposable : (u v : X4) → pluckerRelation (wedge u v) ≡ zer
open PluckerClosureReceipt public

orientedLagrangianFromPair :
  (closure : PluckerClosureReceipt) →
  (u v : X4) →
  symplectic u v ≡ zer →
  NonZeroBivector (wedge u v) →
  OrientedLagrangianBivector
orientedLagrangianFromPair closure u v isotropic nz =
  oriented-lagrangian-bivector
    (wedge u v)
    (isotropicWedgeIsPrimitive u v isotropic)
    (wedgeIsDecomposable closure u v)
    nz

------------------------------------------------------------------------
-- 6. Recognition interfaces.  These are the promotion gates.
------------------------------------------------------------------------

record NullConeRecognition : Set₁ where
  field
    NullCone80 : Set
    toNull : OrientedLagrangianBivector → NullCone80
    fromNull : NullCone80 → OrientedLagrangianBivector
    fromAfterTo : (x : OrientedLagrangianBivector) → fromNull (toNull x) ≡ x
    toAfterFrom : (x : NullCone80) → toNull (fromNull x) ≡ x
open NullConeRecognition public

record SameActionNullConeRecognition : Set₁ where
  field
    Actor : Set
    Derived80 NullCone80 : Set
    actDerived : Actor → Derived80 → Derived80
    actNull : Actor → NullCone80 → NullCone80
    toNull : Derived80 → NullCone80
    fromNull : NullCone80 → Derived80
    fromAfterTo : (x : Derived80) → fromNull (toNull x) ≡ x
    toAfterFrom : (x : NullCone80) → toNull (fromNull x) ≡ x
    intertwines :
      (g : Actor) → (x : Derived80) →
      toNull (actDerived g x) ≡ actNull g (toNull x)
open SameActionNullConeRecognition public

record PGSpWeylRecognition : Set₁ where
  field
    PGSpActor WeylActor : Set
    toWeyl : PGSpActor → WeylActor
    fromWeyl : WeylActor → PGSpActor
    fromAfterTo : (g : PGSpActor) → fromWeyl (toWeyl g) ≡ g
    toAfterFrom : (w : WeylActor) → toWeyl (fromWeyl w) ≡ w
    FiveSpace : Set
    pgspAct : PGSpActor → FiveSpace → FiveSpace
    weylAct : WeylActor → FiveSpace → FiveSpace
    actionIntertwines :
      (g : PGSpActor) → (x : FiveSpace) →
      weylAct (toWeyl g) x ≡ pgspAct g x
open PGSpWeylRecognition public

------------------------------------------------------------------------
-- 7. Local-python computational receipt boundary.
--
-- These booleans record what the exact enumerator checked; they are not used
-- as substitutes for the recognition records above.
------------------------------------------------------------------------

record ExteriorSquareFiniteComputationReceipt : Set where
  constructor exterior-square-finite-computation-receipt
  field
    f3FourNonzeroCount80 : Bool
    orientedLagrangianLiftCount80 : Bool
    projectiveLagrangianLineCount40 : Bool
    projectiveNullPointCount40 : Bool
    projectiveIncidenceGraphSRG401224 : Bool
    e6RootLineGraphSRG361566 : Bool
    gsp4Order103680 : Bool
    projectiveImageOrder51840 : Bool
    reducedE6WeylImageOrder51840 : Bool
    comparedMatrixImagesEqual : Bool
    finiteComputationIsKernelProof : Bool
open ExteriorSquareFiniteComputationReceipt public

canonicalExteriorSquareFiniteComputationReceipt :
  ExteriorSquareFiniteComputationReceipt
canonicalExteriorSquareFiniteComputationReceipt =
  exterior-square-finite-computation-receipt
    true true true true true true true true true true false

------------------------------------------------------------------------
-- 8. Fail-closed status boundary.
------------------------------------------------------------------------

record ExteriorSquareBoundary : Set where
  constructor exterior-square-boundary
  field
    fourTritSymplecticCarrierConstructed : Bool
    wedgeSixCoordinatesConstructed : Bool
    primitiveRelationIsSymplecticWedge : Bool
    primitiveFiveCarrierConstructed : Bool
    orientedLagrangianDerivedCarrierRecorded : Bool
    pluckerClosureInhabitedHere : Bool
    standardDiagonalQ5IsometryInhabitedHere : Bool
    sameActionRecognitionRequired : Bool
    pgspWeylRecognitionInhabitedHere : Bool
    rawPuncturedT4IdentifiedWithNullCone : Bool
    orderEqualityPromotesGroupRecognition : Bool
open ExteriorSquareBoundary public

canonicalExteriorSquareBoundary : ExteriorSquareBoundary
canonicalExteriorSquareBoundary =
  exterior-square-boundary
    true true true true true
    false false true false
    false false
