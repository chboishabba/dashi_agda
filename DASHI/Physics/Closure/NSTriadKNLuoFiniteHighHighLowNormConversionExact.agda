module DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowNormConversionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Prove the exact scale conversion behind HH1 -> HH2.  Write
--
--   lambda_q^(1/2) = h_q,
--   lambda_p^(1/2) = h_p,
--   h_q = rho h_p.
--
-- The elementary projected-product estimate has scale factor
--
--   lambda_q^(3/2) ||f_p||_2 ||g_p||_2 = h_q^3 f g.
--
-- Measuring f in H^(1/2) and g in H^1 gives h_p f and h_p^2 g.
-- Therefore
--
--   h_q^3 f g = rho^3 (h_p f) (h_p^2 g).
--
-- For dyadic gap d, rho=2^(-d/2), hence rho^3=2^(-3d/2).
-- This module closes the norm-conversion algebra; the Fourier Bernstein and
-- Young inequalities that produce the initial projected-product bound remain
-- explicit continuum obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record HighHighScaleGeometry : Set where
  constructor high-high-scale-geometry
  field
    outputHalfScale inputHalfScale halfScaleRatio : ℚ
    outputFromInput :
      outputHalfScale ≡ halfScaleRatio * inputHalfScale

open HighHighScaleGeometry public

projectedProductScale :
  HighHighScaleGeometry → ℚ → ℚ → ℚ
projectedProductScale geometry leftMass rightMass =
  outputHalfScale geometry
  * outputHalfScale geometry
  * outputHalfScale geometry
  * leftMass
  * rightMass

criticalLeftMass :
  HighHighScaleGeometry → ℚ → ℚ
criticalLeftMass geometry leftMass =
  inputHalfScale geometry * leftMass

criticalRightMass :
  HighHighScaleGeometry → ℚ → ℚ
criticalRightMass geometry rightMass =
  inputHalfScale geometry
  * inputHalfScale geometry
  * rightMass

cubicGapCoefficient : HighHighScaleGeometry → ℚ
cubicGapCoefficient geometry =
  halfScaleRatio geometry
  * halfScaleRatio geometry
  * halfScaleRatio geometry

highHighCriticalNormConversion :
  (geometry : HighHighScaleGeometry) →
  (leftMass rightMass : ℚ) →
  projectedProductScale geometry leftMass rightMass
  ≡ cubicGapCoefficient geometry
      * criticalLeftMass geometry leftMass
      * criticalRightMass geometry rightMass
highHighCriticalNormConversion geometry leftMass rightMass
  rewrite outputFromInput geometry =
  solve
    ( halfScaleRatio geometry
    ∷ inputHalfScale geometry
    ∷ leftMass
    ∷ rightMass
    ∷ [])
