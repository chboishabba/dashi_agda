module DASHI.Physics.Closure.NSTriadKNLuoLerayLaplacianCommutationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Verify explicitly that the periodic Leray projector commutes with every
-- scalar Fourier multiplier and hence with the Laplacian and heat semigroup.
-- On a general bounded domain a projection/Laplacian commutator may survive;
-- on the torus both operators act modewise and the commutator is exactly zero.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V

projectCommutesWithScalarMultiplier :
  (modeData : V.ProjectionMode) →
  (multiplier : ℚ) →
  (value : V.Vector3) →
  V.project modeData (V.scale multiplier value)
  ≡ V.scale multiplier (V.project modeData value)
projectCommutesWithScalarMultiplier modeData multiplier value
  with V.mode modeData | value
... | V.v3 mx my mz | V.v3 vx vy vz =
  V.vectorExt
    (solve
      ( multiplier
      ∷ mx ∷ my ∷ mz
      ∷ vx ∷ vy ∷ vz
      ∷ V.inverseNormSquared modeData
      ∷ []))
    (solve
      ( multiplier
      ∷ mx ∷ my ∷ mz
      ∷ vx ∷ vy ∷ vz
      ∷ V.inverseNormSquared modeData
      ∷ []))
    (solve
      ( multiplier
      ∷ mx ∷ my ∷ mz
      ∷ vx ∷ vy ∷ vz
      ∷ V.inverseNormSquared modeData
      ∷ []))

laplacianMultiplier : V.ProjectionMode → ℚ
laplacianMultiplier modeData =
  - V.normSquared (V.mode modeData)

projectCommutesWithLaplacianMode :
  (modeData : V.ProjectionMode) →
  (value : V.Vector3) →
  V.project modeData
    (V.scale (laplacianMultiplier modeData) value)
  ≡ V.scale (laplacianMultiplier modeData)
      (V.project modeData value)
projectCommutesWithLaplacianMode modeData =
  projectCommutesWithScalarMultiplier
    modeData (laplacianMultiplier modeData)

projectCommutesWithHeatMultiplier :
  (modeData : V.ProjectionMode) →
  (heatFactor : ℚ) →
  (value : V.Vector3) →
  V.project modeData (V.scale heatFactor value)
  ≡ V.scale heatFactor (V.project modeData value)
projectCommutesWithHeatMultiplier =
  projectCommutesWithScalarMultiplier
