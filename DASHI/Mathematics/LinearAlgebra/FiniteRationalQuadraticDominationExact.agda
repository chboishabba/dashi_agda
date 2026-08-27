module DASHI.Mathematics.LinearAlgebra.FiniteRationalQuadraticDominationExact where

------------------------------------------------------------------------
-- FINITE RATIONAL QUADRATIC DOMINATION
--
-- PRIMARY SOURCES / CONTEXT
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Nikhil Bansal and Haotian Jiang,
-- "Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlos Bounds
-- Beyond Banaszczyk", STOC 2026.
-- DOI: 10.1145/3798129.3800762.
-- arXiv:2508.03961; DOI: 10.48550/arXiv.2508.03961.
--
-- DASHI CONTRIBUTION
--
-- Several existing repository lanes already prove positive-semidefinite or
-- signed-domination statements by comparing finite quadratic forms:
--
--   * Yang--Mills KKT Gram pseudoinverse positivity;
--   * generated rational LDL^T coercivity certificates;
--   * Navier--Stokes signed good/bad Gram domination; and
--   * covariance / spectral observer constructions.
--
-- This module extracts only their common theorem surface.  It deliberately
-- does NOT introduce another matrix carrier or spectral theorem.  A quadratic
-- form is simply a rational-valued observation of a vector/state carrier, and
-- domination is pointwise order:
--
--   Q <=q R  iff  for every vector x, Q x <= R x.
--
-- Bansal--Jiang affine spectral independence has exactly this theorem shape
-- after translating their Loewner inequality
--
--   E U E^T <= alpha diag(E U E^T)
--
-- into quadratic forms.  The concrete construction of U, E, transpose,
-- covariance transport, diagonal extraction, PSD certificates, and SDP
-- feasibility remains owned by the existing domain-specific matrix layers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

QuadraticForm : Set → Set
QuadraticForm Vector = Vector → ℚ

infix 4 _≼q_

_≼q_ : ∀ {Vector : Set} → QuadraticForm Vector → QuadraticForm Vector → Set
left ≼q right = ∀ vector → left vector ≤ right vector

QuadraticallyEquivalent :
  ∀ {Vector : Set} → QuadraticForm Vector → QuadraticForm Vector → Set
QuadraticallyEquivalent left right = ∀ vector → left vector ≡ right vector

quadraticDominationRefl :
  ∀ {Vector : Set} (form : QuadraticForm Vector) → form ≼q form
quadraticDominationRefl form vector = ℚP.≤-refl

quadraticDominationTrans :
  ∀ {Vector : Set} {first second third : QuadraticForm Vector} →
  first ≼q second → second ≼q third → first ≼q third
quadraticDominationTrans first≤second second≤third vector =
  ℚP.≤-trans (first≤second vector) (second≤third vector)

quadraticEquivalenceGivesForwardDomination :
  ∀ {Vector : Set} {left right : QuadraticForm Vector} →
  QuadraticallyEquivalent left right → left ≼q right
quadraticEquivalenceGivesForwardDomination equivalent vector =
  subst
    (λ selected → _ ≤ selected)
    (equivalent vector)
    ℚP.≤-refl

quadraticEquivalenceGivesBackwardDomination :
  ∀ {Vector : Set} {left right : QuadraticForm Vector} →
  QuadraticallyEquivalent left right → right ≼q left
quadraticEquivalenceGivesBackwardDomination equivalent =
  quadraticEquivalenceGivesForwardDomination
    (λ vector → sym (equivalent vector))

record QuadraticDominationCertificate (Vector : Set) : Set₁ where
  constructor quadraticDominationCertificate
  field
    lower upper : QuadraticForm Vector
    domination : lower ≼q upper

open QuadraticDominationCertificate public

record ExactQuadraticFactorization (Vector Witness : Set) : Set₁ where
  constructor exactQuadraticFactorization
  field
    lower upper : QuadraticForm Vector
    residual : Vector → Witness
    residualNonnegative : Witness → Set
    residualIsNonnegative : ∀ vector → residualNonnegative (residual vector)
    factorization : Set

------------------------------------------------------------------------
-- Claim boundary.
--
-- This order is the theorem-facing interpretation of finite Loewner-style
-- domination, but by itself it does NOT construct:
--   * a covariance operator;
--   * a matrix transpose / adjoint;
--   * a diagonal operator;
--   * a PSD or LDL certificate;
--   * Bansal--Jiang SDP feasibility or Brownian rounding; or
--   * any discrepancy bound.
------------------------------------------------------------------------
