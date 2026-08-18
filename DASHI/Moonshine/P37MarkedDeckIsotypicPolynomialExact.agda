module DASHI.Moonshine.P37MarkedDeckIsotypicPolynomialExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
-- Isotypic decomposition of the regular S3 representation.
--
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
-- Source-facing marked Legendre Hecke correspondences.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full-level-2 frame torsors and deck action.
--
-- DASHI CONTRIBUTION
--
-- P37MarkedDeckIsotypicJointDecompositionExact constructs the actual
-- six-dimensional standard multiplicity block from the source-native p=37
-- permutation orbitals.  Its companion Python verifier discovered three exact
-- polynomial facts, but that module intentionally left them as independently
-- checked factor data.
--
-- This file promotes those FINITE ALGEBRA facts to theorem-level Agda on the
-- same six-dimensional block:
--
--   (1) the T3 annihilating polynomial
--
--       (T3-I)(T3+3I)(T3^2-3T3-I)(T3^2+T3-I) = 0;
--
--   (2) T5 is a rational polynomial in T3:
--
--       34 T5
--         = -38 I -242 T3 +147 T3^2 +158 T3^3 -12 T3^4 -13 T3^5;
--
--   (3) Frobenius/Fricke is a rational polynomial in T3:
--
--       34 F
--         = -7 I -126 T3 +66 T3^2 +115 T3^3 -4 T3^4 -10 T3^5.
--
-- Therefore the joint scalar algebra on this standard multiplicity block is
-- generated already by T3.  Deck representation type remains extra data even
-- when the full T3/T5/F scalar algebra is retained.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Moonshine.P37MarkedDeckIsotypicJointDecompositionExact as Iso

------------------------------------------------------------------------
-- Linear algebra helpers on the existing six-dimensional multiplicity block.
------------------------------------------------------------------------

zero2 : Iso.Std2
zero2 = Iso.std2 0ℚ 0ℚ

zeroStd : Iso.StdBlock3
zeroStd = Iso.stdBlock3 zero2 zero2 zero2

scaleStd : ℚ → Iso.StdBlock3 → Iso.StdBlock3
scaleStd k x = Iso.stdBlock3
  (Iso.scale2 k (Iso.at8 x))
  (Iso.scale2 k (Iso.at0 x))
  (Iso.scale2 k (Iso.at1 x))

addStd : Iso.StdBlock3 → Iso.StdBlock3 → Iso.StdBlock3
addStd = Iso.addStd3

negStd : Iso.StdBlock3 → Iso.StdBlock3
negStd = scaleStd (- 1ℚ)

subStd : Iso.StdBlock3 → Iso.StdBlock3 → Iso.StdBlock3
subStd x y = addStd x (negStd y)

stdExt :
  (x y : Iso.StdBlock3) →
  Iso.u (Iso.at8 x) ≡ Iso.u (Iso.at8 y) →
  Iso.v (Iso.at8 x) ≡ Iso.v (Iso.at8 y) →
  Iso.u (Iso.at0 x) ≡ Iso.u (Iso.at0 y) →
  Iso.v (Iso.at0 x) ≡ Iso.v (Iso.at0 y) →
  Iso.u (Iso.at1 x) ≡ Iso.u (Iso.at1 y) →
  Iso.v (Iso.at1 x) ≡ Iso.v (Iso.at1 y) →
  x ≡ y
stdExt
  (Iso.stdBlock3 (Iso.std2 a b) (Iso.std2 c d) (Iso.std2 e f))
  (Iso.stdBlock3 (Iso.std2 a' b') (Iso.std2 c' d') (Iso.std2 e' f'))
  refl refl refl refl refl refl = refl

------------------------------------------------------------------------
-- Powers of the ACTUAL source-native standard T3 block.
------------------------------------------------------------------------

t3p2 t3p3 t3p4 t3p5 : Iso.StdBlock3 → Iso.StdBlock3
t3p2 x = Iso.standardT3 (Iso.standardT3 x)
t3p3 x = Iso.standardT3 (t3p2 x)
t3p4 x = Iso.standardT3 (t3p3 x)
t3p5 x = Iso.standardT3 (t3p4 x)

------------------------------------------------------------------------
-- T5 and Frobenius are exact polynomials in T3.
------------------------------------------------------------------------

t5Polynomial : Iso.StdBlock3 → Iso.StdBlock3
t5Polynomial x =
  addStd (scaleStd (- (+ 38 / 1)) x)
    (addStd (scaleStd (- (+ 242 / 1)) (Iso.standardT3 x))
      (addStd (scaleStd (+ 147 / 1) (t3p2 x))
        (addStd (scaleStd (+ 158 / 1) (t3p3 x))
          (addStd (scaleStd (- (+ 12 / 1)) (t3p4 x))
                  (scaleStd (- (+ 13 / 1)) (t3p5 x))))))

frobeniusPolynomial : Iso.StdBlock3 → Iso.StdBlock3
frobeniusPolynomial x =
  addStd (scaleStd (- (+ 7 / 1)) x)
    (addStd (scaleStd (- (+ 126 / 1)) (Iso.standardT3 x))
      (addStd (scaleStd (+ 66 / 1) (t3p2 x))
        (addStd (scaleStd (+ 115 / 1) (t3p3 x))
          (addStd (scaleStd (- (+ 4 / 1)) (t3p4 x))
                  (scaleStd (- (+ 10 / 1)) (t3p5 x))))))

standardT5PolynomialExact :
  (x : Iso.StdBlock3) →
  scaleStd (+ 34 / 1) (Iso.standardT5 x) ≡ t5Polynomial x
standardT5PolynomialExact
  (Iso.stdBlock3 (Iso.std2 a b) (Iso.std2 c d) (Iso.std2 e f)) =
  stdExt _ _
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)

standardFrobeniusPolynomialExact :
  (x : Iso.StdBlock3) →
  scaleStd (+ 34 / 1) (Iso.standardF x) ≡ frobeniusPolynomial x
standardFrobeniusPolynomialExact
  (Iso.stdBlock3 (Iso.std2 a b) (Iso.std2 c d) (Iso.std2 e f)) =
  stdExt _ _
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)

------------------------------------------------------------------------
-- Exact factorized annihilator for T3.
------------------------------------------------------------------------

linearOne : Iso.StdBlock3 → Iso.StdBlock3
linearOne x = subStd (Iso.standardT3 x) x

linearNegThree : Iso.StdBlock3 → Iso.StdBlock3
linearNegThree x = addStd (Iso.standardT3 x) (scaleStd (+ 3 / 1) x)

quadraticA : Iso.StdBlock3 → Iso.StdBlock3
quadraticA x =
  subStd
    (subStd (t3p2 x) (scaleStd (+ 3 / 1) (Iso.standardT3 x)))
    x

quadraticB : Iso.StdBlock3 → Iso.StdBlock3
quadraticB x =
  subStd
    (addStd (t3p2 x) (Iso.standardT3 x))
    x

standardT3FactorizedAnnihilatorExact :
  (x : Iso.StdBlock3) →
  linearOne (linearNegThree (quadraticA (quadraticB x))) ≡ zeroStd
standardT3FactorizedAnnihilatorExact
  (Iso.stdBlock3 (Iso.std2 a b) (Iso.std2 c d) (Iso.std2 e f)) =
  stdExt _ _
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)
    (ℚRing.solve-∀ a b c d e f)

------------------------------------------------------------------------
-- Boundary: script-discovered factor data is now internal theorem algebra.
------------------------------------------------------------------------

record P37MarkedDeckIsotypicPolynomialBoundary : Set where
  field
    t3FactorizedAnnihilatorProved : Bool
    t5PolynomialInT3Proved : Bool
    frobeniusPolynomialInT3Proved : Bool
    standardJointScalarAlgebraGeneratedByT3 : Bool
    deckTypeRecoveredFromScalarAlgebra : Bool

canonicalP37MarkedDeckIsotypicPolynomialBoundary :
  P37MarkedDeckIsotypicPolynomialBoundary
canonicalP37MarkedDeckIsotypicPolynomialBoundary = record
  { t3FactorizedAnnihilatorProved = true
  ; t5PolynomialInT3Proved = true
  ; frobeniusPolynomialInT3Proved = true
  ; standardJointScalarAlgebraGeneratedByT3 = true
  ; deckTypeRecoveredFromScalarAlgebra = false
  }
