module DASHI.Mathematics.LinearAlgebra.AffineSpectralIndependenceQuadraticExact where

------------------------------------------------------------------------
-- AFFINE SPECTRAL-INDEPENDENCE AS QUADRATIC DOMINATION
--
-- PRIMARY SOURCE
--
-- Nikhil Bansal and Haotian Jiang,
-- "Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlos Bounds
-- Beyond Banaszczyk", STOC 2026.
-- DOI: 10.1145/3798129.3800762.
-- arXiv:2508.03961; DOI: 10.48550/arXiv.2508.03961.
--
-- Their SDP constrains the covariance U of the update through an affine probe
-- matrix E_s by a Loewner inequality of the form
--
--   E_s U E_s^T <= alpha_s diag(E_s U E_s^T),
--
-- where alpha_s is the relevant r_s / eta_s factor.  On finite real/rational
-- vector carriers, this is exactly the universal quadratic inequality
--
--   <x, E_s U E_s^T x>
--     <=
--   alpha_s <x, diag(E_s U E_s^T) x>.
--
-- DASHI CONTRIBUTION
--
-- This module records precisely that theorem-facing shape using the generic
-- quadratic-domination owner.  It does not own matrix multiplication,
-- covariance construction, diagonal extraction, positivity, SDP feasibility,
-- Brownian rounding, or discrepancy analysis.  Existing DASHI linear-algebra,
-- covariance, LDL, KKT, NS signed-domination, and PNF spectral lanes can all
-- instantiate this one socket.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Mathematics.LinearAlgebra.FiniteRationalQuadraticDominationExact as Q

scaleQuadratic :
  ∀ {Vector : Set} → ℚ → Q.QuadraticForm Vector → Q.QuadraticForm Vector
scaleQuadratic alpha form vector = alpha * form vector

record AffineSpectralIndependenceQuadraticCertificate
    (Vector : Set) : Set₁ where
  constructor affineSpectralIndependenceQuadraticCertificate
  field
    transformedCovarianceQuadratic : Q.QuadraticForm Vector
    diagonalVarianceQuadratic : Q.QuadraticForm Vector
    dominationFactor : ℚ
    affineSpectralDomination :
      transformedCovarianceQuadratic
      Q.≼q
      scaleQuadratic dominationFactor diagonalVarianceQuadratic

open AffineSpectralIndependenceQuadraticCertificate public

asiAsGenericQuadraticDomination :
  ∀ {Vector : Set} →
  AffineSpectralIndependenceQuadraticCertificate Vector →
  Q.QuadraticDominationCertificate Vector
asiAsGenericQuadraticDomination certificate =
  Q.quadraticDominationCertificate
    (transformedCovarianceQuadratic certificate)
    (scaleQuadratic
      (dominationFactor certificate)
      (diagonalVarianceQuadratic certificate))
    (affineSpectralDomination certificate)

------------------------------------------------------------------------
-- CLAIM BOUNDARY
--
-- Inhabiting this record proves only the displayed quadratic domination for
-- the supplied finite forms.  It does not prove that those forms arise from a
-- Bansal--Jiang admissible SDP solution unless a separate bridge constructs
-- them from the actual covariance/probe data and supplies all corresponding
-- feasibility obligations.
------------------------------------------------------------------------
