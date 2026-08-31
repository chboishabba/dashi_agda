module DASHI.Physics.Closure.NSAncientIncrementStretchingAbsorptionNoGoRound66Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Theodore von Karman; Leslie Howarth.
-- Title: "On the Statistical Theory of Isotropic Turbulence".
-- Proceedings of the Royal Society A 164 (1938), 192--215.
-- DOI: 10.1098/rspa.1938.0013.
--
-- Authors: Jean Duchon; Raoul Robert.
-- Title: "Inertial energy dissipation for weak solutions of incompressible
--         Euler and Navier-Stokes equations".
-- Nonlinearity 13 (2000), 249--255.
-- DOI: 10.1088/0951-7715/13/1/312.
--
-- ROUND66 / INCREMENT STRETCHING: SIGN + HOMOGENEITY NO-GO
--
-- Round66 reduced the global increment-energy identity to
--
--   E'_h + nu D_h = - integral w^T S(u) w.
--
-- This file proves two exact obstructions to treating the surviving term by a
-- bare absolute/instantaneous estimate.
--
-- 1. Incompressibility only says tr S = 0.  A trace-free strain can make
--    w^T S w either +1 or -1 on the same increment direction.  Hence the
--    increment production -w^T S w has either sign.
--
-- 2. Under the Navier--Stokes amplitude scaling u -> a u at fixed geometry,
--    w -> a w and grad u -> a grad u.  Thus stretching is cubic (a^3), while
--    increment dissipation is quadratic (a^2).  No fixed coefficient theta
--    can absorb positive cubic production into quadratic dissipation for all
--    amplitudes.
--
-- Therefore the increment route only advances C if it exploits a genuinely
-- signed/nonlocal/scale-space cancellation (Karman--Howarth/Duchon--Robert
-- type), geometric depletion, or another property of the ancient blow-up
-- class.  It does not evade the earlier homogeneity obstruction by itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; -_; _+_; _*_; _≤_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSAncientIncrementEnergyStrainReductionRound66Exact as Inc

trace : Inc.Gradient3 → ℚ
trace G = Inc.g11 G + Inc.g22 G + Inc.g33 G

extensionalStrain : Inc.Gradient3
extensionalStrain = Inc.grad3
  1ℚ 0ℚ 0ℚ
  0ℚ (- 1ℚ) 0ℚ
  0ℚ 0ℚ 0ℚ

compressiveStrain : Inc.Gradient3
compressiveStrain = Inc.grad3
  (- 1ℚ) 0ℚ 0ℚ
  0ℚ 1ℚ 0ℚ
  0ℚ 0ℚ 0ℚ

unitIncrementX : Inc.Vector3
unitIncrementX = Inc.v3 1ℚ 0ℚ 0ℚ

extensionalStrainTraceFree : trace extensionalStrain ≡ 0ℚ
extensionalStrainTraceFree = refl

compressiveStrainTraceFree : trace compressiveStrain ≡ 0ℚ
compressiveStrainTraceFree = refl

extensionalStretchingPositive :
  Inc.incrementStretching extensionalStrain unitIncrementX ≡ 1ℚ
extensionalStretchingPositive = refl

compressiveStretchingNegative :
  Inc.incrementStretching compressiveStrain unitIncrementX ≡ - 1ℚ
compressiveStretchingNegative = refl

-- The energy RHS is minus the stretching contraction.  Thus the compressive
-- witness gives strictly positive increment-energy production.
compressiveIncrementEnergyProductionPositive :
  - Inc.incrementStretching compressiveStrain unitIncrementX ≡ 1ℚ
compressiveIncrementEnergyProductionPositive = refl

square : ℚ → ℚ
square a = a * a

cubic : ℚ → ℚ
cubic a = a * square a

incrementStretchingScale : ℚ → ℚ
incrementStretchingScale = cubic

incrementDissipationScale : ℚ → ℚ
incrementDissipationScale = square

fixedQuadraticAbsorptionFailsAboveAmplitude :
  (theta a : ℚ) →
  0ℚ < square a →
  theta < a →
  ¬ (incrementStretchingScale a
      ≤ theta * incrementDissipationScale a)
fixedQuadraticAbsorptionFailsAboveAmplitude theta a squarePositive thetaBelowA proposed =
  let
    instance squarePos : Positive (square a)
        squarePos = positive squarePositive

    scaledStrict : theta * square a < a * square a
    scaledStrict = ℚP.*-monoʳ-<-pos (square a) thetaBelowA
  in
  ℚP.<-irrefl (theta * square a)
    (ℚP.<-≤-trans scaledStrict proposed)
