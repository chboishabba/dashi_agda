module DASHI.Mathematics.LinearAlgebra.RationalAffineSpectralIndependence2Exact where

------------------------------------------------------------------------
-- RATIONAL 2x2 AFFINE SPECTRAL-INDEPENDENCE SEED
--
-- PRIMARY SOURCE / CONTEXT
--
-- Nikhil Bansal and Haotian Jiang,
-- "Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlos Bounds
-- Beyond Banaszczyk", STOC 2026, DOI 10.1145/3798129.3800762;
-- arXiv:2508.03961, DOI 10.48550/arXiv.2508.03961.
--
-- Their affine spectral-independence SDP uses, for covariance U and an affine
-- probe matrix E_s, the constraint
--
--   E_s U E_s^T <= (r_s / eta_s) diag(E_s U E_s^T)
--
-- in Loewner order, together with U >= 0.  Equivalently, every linear
-- combination of the probed update coordinates has variance controlled by the
-- corresponding diagonal variance sum (paper, Section 2.4.1, equations 14--16).
--
-- Roger A. Horn and Charles R. Johnson, "Matrix Analysis", second edition,
-- Cambridge University Press, 2012, DOI 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Reuse the existing exact rational self-adjoint 2x2 carrier to construct one
-- theorem-bearing special case of the Bansal--Jiang transformed covariance.
-- With identity covariance and the orthogonal signed probe rows (1,1) and
-- (1,-1), E U E^T is exactly diag(2,2).  Hence the off-diagonal coupling is
-- exactly zero and factor-one diagonal domination holds by equality.
--
-- This is intentionally only a finite algebraic seed.  It does NOT formalize
-- general Loewner order, PSD feasibility of the Bansal--Jiang SDP, random
-- covariance, Brownian rounding, tail bounds, or their Komlos/Beck-Fiala
-- theorems.  Equality with the diagonal is stronger than the required
-- factor-one domination for this single displayed example.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.LinearAlgebra.RationalTwoByTwoSelfAdjointSpectralExact as LA

minusOne : ℚ
minusOne = 0ℚ - 1ℚ

two : ℚ
two = 1ℚ + 1ℚ

multiply : LA.Matrix2 → LA.Matrix2 → LA.Matrix2
multiply
  (LA.matrix2 a b c d)
  (LA.matrix2 e f g h) =
  LA.matrix2
    (a * e + b * g)
    (a * f + b * h)
    (c * e + d * g)
    (c * f + d * h)

identityCovariance : LA.Matrix2
identityCovariance = LA.matrix2 1ℚ 0ℚ 0ℚ 1ℚ

signedOrthogonalProbe : LA.Matrix2
signedOrthogonalProbe = LA.matrix2 1ℚ 1ℚ 1ℚ minusOne

transformedCovariance : LA.Matrix2 → LA.Matrix2 → LA.Matrix2
transformedCovariance probe covariance =
  multiply (multiply probe covariance) (LA.transpose probe)

diagonalPart : LA.Matrix2 → LA.Matrix2
diagonalPart matrix =
  LA.matrix2
    (LA.entry11 matrix)
    0ℚ
    0ℚ
    (LA.entry22 matrix)

expectedTransformedCovariance : LA.Matrix2
expectedTransformedCovariance = LA.matrix2 two 0ℚ 0ℚ two

signedProbeTransformsIdentityToDiagonalTwo :
  transformedCovariance signedOrthogonalProbe identityCovariance
  ≡ expectedTransformedCovariance
signedProbeTransformsIdentityToDiagonalTwo =
  LA.matrixExtensionality
    (solve [])
    (solve [])
    (solve [])
    (solve [])

transformedCovarianceEqualsItsDiagonalPart :
  transformedCovariance signedOrthogonalProbe identityCovariance
  ≡ diagonalPart
      (transformedCovariance signedOrthogonalProbe identityCovariance)
transformedCovarianceEqualsItsDiagonalPart =
  LA.matrixExtensionality
    (solve [])
    (solve [])
    (solve [])
    (solve [])

transformedOffDiagonalExactlyZero :
  LA.entry12
    (transformedCovariance signedOrthogonalProbe identityCovariance) ≡ 0ℚ
  ×
  LA.entry21
    (transformedCovariance signedOrthogonalProbe identityCovariance) ≡ 0ℚ
transformedOffDiagonalExactlyZero = solve [] , solve []

------------------------------------------------------------------------
-- Exact finite factor-one certificate.
--
-- For the displayed rational example, transformed covariance equals its
-- diagonal part.  Therefore any future generic Loewner-order implementation
-- can obtain the Bansal--Jiang factor-one inequality by reflexivity/order
-- weakening, without changing this algebraic theorem.
------------------------------------------------------------------------

record FactorOneAffineSpectralIndependence2 : Set where
  constructor factorOneAffineSpectralIndependence2
  field
    covariance : LA.Matrix2
    affineProbe : LA.Matrix2
    transformedIsDiagonal :
      transformedCovariance affineProbe covariance
      ≡ diagonalPart (transformedCovariance affineProbe covariance)

open FactorOneAffineSpectralIndependence2 public

canonicalFactorOneAffineSpectralIndependence2 :
  FactorOneAffineSpectralIndependence2
canonicalFactorOneAffineSpectralIndependence2 =
  factorOneAffineSpectralIndependence2
    identityCovariance
    signedOrthogonalProbe
    transformedCovarianceEqualsItsDiagonalPart

record RationalAffineSpectralIndependenceBoundary : Set where
  constructor rationalAffineSpectralIndependenceBoundary
  field
    transformedCovarianceConstructed : Bool
    transformedCovarianceConstructedIsTrue :
      transformedCovarianceConstructed ≡ true
    exactOffDiagonalDecouplingConstructed : Bool
    exactOffDiagonalDecouplingConstructedIsTrue :
      exactOffDiagonalDecouplingConstructed ≡ true
    generalLoewnerOrderFormalizedHere : Bool
    generalLoewnerOrderFormalizedHereIsFalse :
      generalLoewnerOrderFormalizedHere ≡ false
    bansalJiangSDPFeasibilityPromoted : Bool
    bansalJiangSDPFeasibilityPromotedIsFalse :
      bansalJiangSDPFeasibilityPromoted ≡ false

canonicalRationalAffineSpectralIndependenceBoundary :
  RationalAffineSpectralIndependenceBoundary
canonicalRationalAffineSpectralIndependenceBoundary =
  rationalAffineSpectralIndependenceBoundary
    true refl
    true refl
    false refl
    false refl
