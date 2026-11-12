module DASHI.Analysis.RiemannXiSymmetricMellinPolynomialExact where

------------------------------------------------------------------------
-- P3: ORIGINAL rational-coordinate functional reflection, together
-- with the EXACT polynomial normalization s(s-1).
--
-- The user-supplied theta/Mellin expression has form
--   1/2 + (s(s-1)/2) * T(s)
-- where T(s)=integral_1^infty
--       (t^(s/2)+t^((1-s)/2)) (theta(t)-1)/(2t) dt.
--
-- THIS FILE PAYS ONLY the original rational-complex polynomial
-- reflection and the exact algebraic symmetry transfer for a
-- separately supplied T(s)=T(1-s).
--
-- Realization of T as the ORIGINAL Bishop Mellin integral, Jacobi
-- theta modular inversion, convergence/entireness, Gamma identity,
-- and identification with the original CompletedRiemannZeta.xi
-- remain independently OPEN. No synthetic xi is promoted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; trans)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (0ℚ; 1ℚ)
import Data.Rational as Rational using (_/_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact as Original
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD

rationalCoordinateComplex :
  Original.ComplexCoordinate → CD.RationalComplex
rationalCoordinateComplex point =
  CD.complex (Original.realPart point)
             (Original.imaginaryPart point)

originalXiPolynomial :
  Original.ComplexCoordinate → CD.RationalComplex
originalXiPolynomial point =
  CD._*c_
    (rationalCoordinateComplex point)
    (CD._-c_ (rationalCoordinateComplex point) CD.oneC)

-- This polynomial has the CORRECT completed-Xi normalization.
-- A similar statement about s or s-1 individually would be false.
originalXiPolynomialFunctionalReflection :
  (point : Original.ComplexCoordinate) →
  originalXiPolynomial point
  ≡ originalXiPolynomial (Original.functionalReflection point)
originalXiPolynomialFunctionalReflection
    (Original.complexCoordinate sigma tau) =
  CD.complexExt Ring.solve-∀ Ring.solve-∀

halfComplex : CD.RationalComplex
halfComplex = CD.complex ((+ 1) Rational./ 2) 0ℚ

-- For an eventual separately selected Mellin tail, use the same
-- original rational complex arithmetic and original reflection.
normalizedSymmetricMellinKernel :
  (Original.ComplexCoordinate → CD.RationalComplex) →
  Original.ComplexCoordinate → CD.RationalComplex
normalizedSymmetricMellinKernel tail point =
  CD._+c_ halfComplex
    (CD._*c_ halfComplex
      (CD._*c_ (originalXiPolynomial point) (tail point)))

originalXiPolynomialAndTailReflection :
  (tail : Original.ComplexCoordinate → CD.RationalComplex) →
  ((point : Original.ComplexCoordinate) →
    tail point ≡ tail (Original.functionalReflection point)) →
  (point : Original.ComplexCoordinate) →
  normalizedSymmetricMellinKernel tail point
  ≡ normalizedSymmetricMellinKernel tail
      (Original.functionalReflection point)
originalXiPolynomialAndTailReflection tail symmetry point =
  cong
    (λ product → CD._+c_ halfComplex
      (CD._*c_ halfComplex product))
    (cong₂ CD._*c_
      (originalXiPolynomialFunctionalReflection point)
      (symmetry point))

-- No inhabitant of the separately required *actual* original
-- theta/Mellin tail, Gamma integral, continuation or xi semantic
-- identification is invented by this finite polynomial proof.
