module DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact where

------------------------------------------------------------------------
-- RATIONAL ALBERT / H_3(O_Q) CARRIER AND CUBIC NORM
--
-- Primary background:
--   Richard D. Schafer, An Introduction to Nonassociative Algebras (1966).
--   John C. Baez, "The Octonions", Bull. AMS 39 (2002), 145--205,
--   DOI 10.1090/S0273-0979-01-00934-X.
--
-- DASHI contribution:
--
-- Reuse the repository's exact rational octonion carrier to construct the
-- 27-coordinate Hermitian 3x3 carrier
--
--     H_3(O_Q) = Q^3 + O_Q^3,
--
-- with 3 + 3*8 = 27 rational coordinates, distinguished identity, trace, and
-- the standard cubic determinant/norm
--
--     N(a,b,c;x,y,z)
--       = abc - a n(x) - b n(y) - c n(z)
--         + 2 Re((x y) z).
--
-- The coordinate convention is the standard Hermitian matrix shape
--
--       [ a       z       conjugate(y) ]
--       [ conjugate(z) b  x            ]
--       [ y       conjugate(x) c       ].
--
-- This file deliberately stops before claiming the exceptional Jordan
-- identity or F4 automorphism recognition.  Those require the symmetrised
-- Hermitian matrix product/closure proof (or an equivalent adjoint identity),
-- not cardinality 27.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O

------------------------------------------------------------------------
-- Exact 27-coordinate Hermitian carrier.
------------------------------------------------------------------------

record RationalAlbert : Set where
  constructor albert
  field
    diagonal0 diagonal1 diagonal2 : ℚ
    off12 off20 off01 : O.RationalOctonion
open RationalAlbert public

zeroAlbert unitAlbert : RationalAlbert
zeroAlbert = albert 0ℚ 0ℚ 0ℚ O.zeroO O.zeroO O.zeroO
unitAlbert = albert 1ℚ 1ℚ 1ℚ O.zeroO O.zeroO O.zeroO

_+A_ : RationalAlbert → RationalAlbert → RationalAlbert
albert a b c x y z +A albert a' b' c' x' y' z' =
  albert
    (a + a') (b + b') (c + c')
    (O._+o_ x x') (O._+o_ y y') (O._+o_ z z')

negA : RationalAlbert → RationalAlbert
negA (albert a b c x y z) =
  albert (- a) (- b) (- c) (O.negO x) (O.negO y) (O.negO z)

scaleQ : ℚ → Q.RationalQuaternion → Q.RationalQuaternion
scaleQ scalar (Q.quat q0 q1 q2 q3) =
  Q.quat (scalar * q0) (scalar * q1) (scalar * q2) (scalar * q3)

scaleO : ℚ → O.RationalOctonion → O.RationalOctonion
scaleO scalar (O.oct first second) =
  O.oct (scaleQ scalar first) (scaleQ scalar second)

scaleA : ℚ → RationalAlbert → RationalAlbert
scaleA scalar (albert a b c x y z) =
  albert
    (scalar * a) (scalar * b) (scalar * c)
    (scaleO scalar x) (scaleO scalar y) (scaleO scalar z)

------------------------------------------------------------------------
-- Coordinate dimension: 3 real/rational diagonal coordinates plus three
-- eight-coordinate octonions.
------------------------------------------------------------------------

octonionCoordinateDimension : Nat
octonionCoordinateDimension = 8

albertCoordinateDimension : Nat
albertCoordinateDimension = 3 + 3 * octonionCoordinateDimension

albertCoordinateDimensionIsTwentySeven : albertCoordinateDimension ≡ 27
albertCoordinateDimensionIsTwentySeven = refl

------------------------------------------------------------------------
-- Trace and cubic determinant/norm.
------------------------------------------------------------------------

traceA : RationalAlbert → ℚ
traceA (albert a b c _ _ _) = a + b + c

realPartO : O.RationalOctonion → ℚ
realPartO (O.oct (Q.quat scalar _ _ _) _) = scalar

tripleReal : O.RationalOctonion → O.RationalOctonion → O.RationalOctonion → ℚ
tripleReal x y z = realPartO (O._*o_ (O._*o_ x y) z)

cubicNorm : RationalAlbert → ℚ
cubicNorm (albert a b c x y z) =
  (a * b * c)
  + ((1ℚ + 1ℚ) * tripleReal x y z)
  + (- (a * O.octonionNormSq x))
  + (- (b * O.octonionNormSq y))
  + (- (c * O.octonionNormSq z))

------------------------------------------------------------------------
-- Distinguished identity checks available before the Jordan product itself.
------------------------------------------------------------------------

traceUnit : traceA unitAlbert ≡ 1ℚ + 1ℚ + 1ℚ
traceUnit = refl

cubicNormUnit : cubicNorm unitAlbert ≡ 1ℚ
cubicNormUnit = solve []

cubicNormZero : cubicNorm zeroAlbert ≡ 0ℚ
cubicNormZero = solve []

------------------------------------------------------------------------
-- Exact frontier: the carrier and cubic invariant now exist.  The missing
-- theorem is algebraic, not cardinal: construct the Hermitian Jordan product
-- and prove closure/Jordan identity, then identify its automorphism action.
------------------------------------------------------------------------

record RationalAlbertCubicPackage : Set where
  constructor rational-albert-cubic-package
  field
    Carrier : Set
    zero unit : Carrier
    add : Carrier → Carrier → Carrier
    neg : Carrier → Carrier
    scale : ℚ → Carrier → Carrier
    trace : Carrier → ℚ
    norm3 : Carrier → ℚ
    coordinateDimension : Nat
    coordinateDimension27 : coordinateDimension ≡ 27
open RationalAlbertCubicPackage public

rationalAlbertCubicPackage : RationalAlbertCubicPackage
rationalAlbertCubicPackage =
  rational-albert-cubic-package
    RationalAlbert
    zeroAlbert unitAlbert _+A_ negA scaleA traceA cubicNorm
    albertCoordinateDimension albertCoordinateDimensionIsTwentySeven

record AlbertJordanFrontier : Set where
  constructor albert-jordan-frontier
  field
    rationalHermitianCarrierPaid : Bool
    coordinateDimension27Paid : Bool
    distinguishedIdentityPaid : Bool
    tracePaid : Bool
    cubicNormPaid : Bool
    identityCubicNormOnePaid : Bool
    jordanProductPaid : Bool
    hermitianProductClosurePaid : Bool
    jordanIdentityPaid : Bool
    f4AutomorphismActionPaid : Bool
open AlbertJordanFrontier public

currentAlbertJordanFrontier : AlbertJordanFrontier
currentAlbertJordanFrontier =
  albert-jordan-frontier
    true true true true true true
    false false false false
