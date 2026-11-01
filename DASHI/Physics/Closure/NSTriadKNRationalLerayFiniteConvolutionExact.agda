module DASHI.Physics.Closure.NSTriadKNRationalLerayFiniteConvolutionExact where

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
-- Lift the exact rational Leray multiplier from one vector to a complete finite
-- convolution fold.  The rank-one formula is proved additive and homogeneous;
-- hence projection commutes with the recursively defined finite sum.  The
-- projected coefficient is transverse and its squared norm is bounded by the
-- unprojected convolution coefficient.  No projector-contraction estimate is
-- supplied as a convolution-level field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as Leray

zeroVector : Leray.Vector3
zeroVector = Leray.v3 0ℚ 0ℚ 0ℚ

projectZero :
  (data : Leray.ProjectionMode) →
  Leray.project data zeroVector ≡ zeroVector
projectZero data with Leray.mode data
... | Leray.v3 mx my mz =
  Leray.vectorExt
    (solve (mx ∷ my ∷ mz ∷ Leray.inverseNormSquared data ∷ []))
    (solve (mx ∷ my ∷ mz ∷ Leray.inverseNormSquared data ∷ []))
    (solve (mx ∷ my ∷ mz ∷ Leray.inverseNormSquared data ∷ []))

projectAdd :
  (data : Leray.ProjectionMode) →
  (left right : Leray.Vector3) →
  Leray.project data (Leray.add left right)
  ≡ Leray.add (Leray.project data left) (Leray.project data right)
projectAdd data left right
  with Leray.mode data | left | right
... | Leray.v3 mx my mz
    | Leray.v3 lx ly lz
    | Leray.v3 rx ry rz =
  Leray.vectorExt
    (solve
      ( mx ∷ my ∷ mz
      ∷ lx ∷ ly ∷ lz
      ∷ rx ∷ ry ∷ rz
      ∷ Leray.inverseNormSquared data
      ∷ []))
    (solve
      ( mx ∷ my ∷ mz
      ∷ lx ∷ ly ∷ lz
      ∷ rx ∷ ry ∷ rz
      ∷ Leray.inverseNormSquared data
      ∷ []))
    (solve
      ( mx ∷ my ∷ mz
      ∷ lx ∷ ly ∷ lz
      ∷ rx ∷ ry ∷ rz
      ∷ Leray.inverseNormSquared data
      ∷ []))

projectScale :
  (data : Leray.ProjectionMode) →
  (scalar : ℚ) →
  (value : Leray.Vector3) →
  Leray.project data (Leray.scale scalar value)
  ≡ Leray.scale scalar (Leray.project data value)
projectScale data scalar value
  with Leray.mode data | value
... | Leray.v3 mx my mz | Leray.v3 vx vy vz =
  Leray.vectorExt
    (solve
      ( scalar ∷ mx ∷ my ∷ mz
      ∷ vx ∷ vy ∷ vz
      ∷ Leray.inverseNormSquared data
      ∷ []))
    (solve
      ( scalar ∷ mx ∷ my ∷ mz
      ∷ vx ∷ vy ∷ vz
      ∷ Leray.inverseNormSquared data
      ∷ []))
    (solve
      ( scalar ∷ mx ∷ my ∷ mz
      ∷ vx ∷ vy ∷ vz
      ∷ Leray.inverseNormSquared data
      ∷ []))

vectorSum : List Leray.Vector3 → Leray.Vector3
vectorSum [] = zeroVector
vectorSum (value ∷ values) = Leray.add value (vectorSum values)

projectEach :
  Leray.ProjectionMode →
  List Leray.Vector3 →
  List Leray.Vector3
projectEach data [] = []
projectEach data (value ∷ values) =
  Leray.project data value ∷ projectEach data values

projectCommutesWithFiniteSum :
  (data : Leray.ProjectionMode) →
  (values : List Leray.Vector3) →
  Leray.project data (vectorSum values)
  ≡ vectorSum (projectEach data values)
projectCommutesWithFiniteSum data [] = projectZero data
projectCommutesWithFiniteSum data (value ∷ values) =
  trans
    (projectAdd data value (vectorSum values))
    (cong
      (Leray.add (Leray.project data value))
      (projectCommutesWithFiniteSum data values))

projectedFiniteConvolutionCoefficient :
  Leray.ProjectionMode →
  List Leray.Vector3 →
  Leray.Vector3
projectedFiniteConvolutionCoefficient data contributions =
  Leray.project data (vectorSum contributions)

projectedFiniteConvolutionIsTransverse :
  (data : Leray.ProjectionMode) →
  (contributions : List Leray.Vector3) →
  Leray.dot
    (Leray.mode data)
    (projectedFiniteConvolutionCoefficient data contributions)
  ≡ 0ℚ
projectedFiniteConvolutionIsTransverse data contributions =
  Leray.projectTransverse data (vectorSum contributions)

projectedFiniteConvolutionContractionSquared :
  (data : Leray.ProjectionMode) →
  (contributions : List Leray.Vector3) →
  Leray.normSquared
    (projectedFiniteConvolutionCoefficient data contributions)
  ≤ Leray.normSquared (vectorSum contributions)
projectedFiniteConvolutionContractionSquared data contributions =
  Leray.projectContractionSquared data (vectorSum contributions)

rationalLerayFiniteConvolutionClosed : Bool
rationalLerayFiniteConvolutionClosed = true

rationalLerayFiniteConvolutionClosedIsTrue :
  rationalLerayFiniteConvolutionClosed ≡ true
rationalLerayFiniteConvolutionClosedIsTrue = refl
