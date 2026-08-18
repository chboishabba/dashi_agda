module DASHI.Moonshine.SupersingularFrobeniusFrickeGenusReductionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974--1975), expose 7.
-- MR 417184; no DOI asserted.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
-- Fricke genus / supersingular rationality context.
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", 2nd ed., Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
-- Supersingular elliptic curves and Frobenius context.
--
-- John Voight,
-- "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapter 42, supersingular elliptic curves and quaternionic descriptions.
--
-- DASHI CONTRIBUTION
--
-- Compress the remaining global Frobenius/Ogg geometry to its genuinely
-- geometric inputs.  Suppose a prime-level situation supplies:
--
--   S = total number of supersingular geometric j-classes,
--   r = number fixed by arithmetic Frobenius / rational over F_p,
--   d = number of nontrivial Frobenius two-orbits,
--   g = genus X0(p),
--   g+ = genus X0+(p),
--   R = number of Fricke fixed points on X0(p).
--
-- If
--
--   S = g + 1,                 (supersingular count)
--   S = r + 2 d,               (actual Frobenius orbit decomposition)
--   R = 2 r,                   (Fricke fixed points vs rational ss classes)
--   4 g+ + R = 2 g + 2,        (Riemann--Hurwitz for the Fricke quotient)
--
-- then elementary Nat arithmetic forces
--
--   d = g+.
--
-- Thus the remaining global theorem is NOT another finite Ogg scan.  It is the
-- source-native geometric construction of these count identities on the same
-- supersingular/Fricke carriers, especially R = 2 r.  Once those are supplied,
-- paired Frobenius defect = Fricke quotient genus is formal algebra.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
import Data.Nat.Properties as Nat
import Data.Nat.Tactic.RingSolver as NatRing

record SupersingularFrickeCountData : Set where
  field
    totalSupersingular : Nat
    rationalSupersingular : Nat
    frobeniusPairDefect : Nat
    genusX0 : Nat
    genusX0Plus : Nat
    frickeFixedPoints : Nat

    totalIsGenusPlusOne :
      totalSupersingular ≡ genusX0 + 1

    frobeniusOrbitDecomposition :
      totalSupersingular
      ≡ rationalSupersingular + 2 * frobeniusPairDefect

    frickeFixedDoubleRational :
      frickeFixedPoints ≡ 2 * rationalSupersingular

    frickeRiemannHurwitz :
      4 * genusX0Plus + frickeFixedPoints
      ≡ 2 * genusX0 + 2

open SupersingularFrickeCountData public

------------------------------------------------------------------------
-- First expose the equality before cancellation.  This is useful to consumers
-- that prefer subtraction-free cardinality identities.
------------------------------------------------------------------------

fourTimesGenusPlusEqualsFourTimesPairDefect :
  (D : SupersingularFrickeCountData) →
  4 * genusX0Plus D ≡ 4 * frobeniusPairDefect D
fourTimesGenusPlusEqualsFourTimesPairDefect D =
  Nat.+-cancelʳ-≡
    (4 * genusX0Plus D)
    (4 * frobeniusPairDefect D)
    (2 * rationalSupersingular D)
    balanced
  where
  rhWithRational :
    4 * genusX0Plus D + 2 * rationalSupersingular D
    ≡ 2 * genusX0 D + 2
  rhWithRational =
    trans
      (cong (4 * genusX0Plus D +_) (sym (frickeFixedDoubleRational D)))
      (frickeRiemannHurwitz D)

  rhsAsTwiceTotal :
    2 * genusX0 D + 2 ≡ 2 * totalSupersingular D
  rhsAsTwiceTotal =
    trans
      (NatRing.solve (genusX0 D ∷ []))
      (sym (cong (2 *_) (totalIsGenusPlusOne D)))

  twiceTotalAsOrbitCount :
    2 * totalSupersingular D
    ≡ 2 * rationalSupersingular D + 4 * frobeniusPairDefect D
  twiceTotalAsOrbitCount =
    trans
      (cong (2 *_) (frobeniusOrbitDecomposition D))
      (NatRing.solve
        (rationalSupersingular D ∷ frobeniusPairDefect D ∷ []))

  balanced0 :
    4 * genusX0Plus D + 2 * rationalSupersingular D
    ≡ 2 * rationalSupersingular D + 4 * frobeniusPairDefect D
  balanced0 = trans rhWithRational (trans rhsAsTwiceTotal twiceTotalAsOrbitCount)

  balanced :
    4 * genusX0Plus D + 2 * rationalSupersingular D
    ≡ 4 * frobeniusPairDefect D + 2 * rationalSupersingular D
  balanced =
    trans balanced0
      (Nat.+-comm
        (2 * rationalSupersingular D)
        (4 * frobeniusPairDefect D))

------------------------------------------------------------------------
-- Main reduction theorem.
------------------------------------------------------------------------

frobeniusPairDefectEqualsFrickeGenus :
  (D : SupersingularFrickeCountData) →
  frobeniusPairDefect D ≡ genusX0Plus D
frobeniusPairDefectEqualsFrickeGenus D =
  sym
    (Nat.*-cancelˡ-≡
      (genusX0Plus D)
      (frobeniusPairDefect D)
      4
      (fourTimesGenusPlusEqualsFourTimesPairDefect D))

zeroPairDefectIffZeroFrickeGenus :
  (D : SupersingularFrickeCountData) →
  frobeniusPairDefect D ≡ 0 ↔ genusX0Plus D ≡ 0
zeroPairDefectIffZeroFrickeGenus D =
  (λ pairZero → trans (sym (frobeniusPairDefectEqualsFrickeGenus D)) pairZero)
  ,
  (λ genusZero → trans (frobeniusPairDefectEqualsFrickeGenus D) genusZero)

------------------------------------------------------------------------
-- Boundary: algebraic globalization is closed; carrier-specific geometric
-- count theorems remain the real source-facing producer.
------------------------------------------------------------------------

record SupersingularFrobeniusFrickeGenusReductionBoundary : Set where
  field
    subtractionFreeReductionConstructed : Bool
    pairDefectEqualsFrickeGenusDerived : Bool
    zeroDefectIffGenusZeroDerived : Bool
    frickeFixedDoubleRationalProvedGeometricallyHere : Bool
    totalSupersingularEqualsGenusPlusOneProvedGeometricallyHere : Bool
    globalOggTheoremClaimedHere : Bool

canonicalSupersingularFrobeniusFrickeGenusReductionBoundary :
  SupersingularFrobeniusFrickeGenusReductionBoundary
canonicalSupersingularFrobeniusFrickeGenusReductionBoundary = record
  { subtractionFreeReductionConstructed = true
  ; pairDefectEqualsFrickeGenusDerived = true
  ; zeroDefectIffGenusZeroDerived = true
  ; frickeFixedDoubleRationalProvedGeometricallyHere = false
  ; totalSupersingularEqualsGenusPlusOneProvedGeometricallyHere = false
  ; globalOggTheoremClaimedHere = false
  }
