module DASHI.Physics.Closure.NSTriadKNPointwiseStrainVorticityLowerBoundNoGoRound79Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Andrea Cavazzini.
-- Title: "Self-Frustration of Vortex Stretching and the Architecture of the
-- Navier-Stokes Blow-Up Barrier".
-- Zenodo preprint (2026).
-- DOI: 10.5281/zenodo.19158797.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- DOI: 10.1007/BF01240221.
--
-- ROUND79 / DENOMINATOR NO-GO
--
-- A tempting eigenframe-injection estimate divides an off-diagonal pressure
-- Hessian bound by a strain spectral gap and then asserts the gap is bounded
-- below by a positive multiple of the vorticity maximum. That lower bound does
-- not follow pointwise from incompressibility/trace-free strain.
--
-- The smooth periodic divergence-free field
--
--   u(x,y,z) = (-sin y, sin x, 0)
--
-- has at the origin
--
--   grad u = [ 0 -1 0 ; 1 0 0 ; 0 0 0 ],
--   S = (grad u + grad u^T)/2 = 0,
--   omega = curl u = (0,0,2).
--
-- Moreover |omega| reaches its global maximum 2 at the origin.  The exact
-- rational jet below proves the algebraic core: a nonzero vorticity maximum can
-- coexist with zero strain and hence zero strain spectral gaps. Therefore no
-- theorem may silently use |S| >= c |omega| (c>0), or g_j3 >= c M, without a
-- genuinely additional physical hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M

record GradientJet : Set where
  constructor gradient-jet
  field
    g11 g12 g13 : ℚ
    g21 g22 g23 : ℚ
    g31 g32 g33 : ℚ

open GradientJet public

trace : GradientJet → ℚ
trace g = g11 g + g22 g + g33 g

symmetricNumerator : GradientJet → M.Matrix3
symmetricNumerator g = M.matrix3
  (g11 g + g11 g)
  (g12 g + g21 g)
  (g13 g + g31 g)
  (g21 g + g12 g)
  (g22 g + g22 g)
  (g23 g + g32 g)
  (g31 g + g13 g)
  (g32 g + g23 g)
  (g33 g + g33 g)

vorticity : GradientJet → V.Vector3
vorticity g = V.v3
  (g32 g - g23 g)
  (g13 g - g31 g)
  (g21 g - g12 g)

periodicPureRotationOriginJet : GradientJet
periodicPureRotationOriginJet = gradient-jet
  0ℚ (- 1ℚ) 0ℚ
  1ℚ 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ

originJetIsIncompressible : trace periodicPureRotationOriginJet ≡ 0ℚ
originJetIsIncompressible = refl

originSymmetricNumeratorZero :
  symmetricNumerator periodicPureRotationOriginJet ≡ M.zeroMatrix
originSymmetricNumeratorZero =
  M.matrixExt refl refl refl refl refl refl refl refl refl

originVorticityExact :
  vorticity periodicPureRotationOriginJet ≡ V.v3 0ℚ 0ℚ (1ℚ + 1ℚ)
originVorticityExact = refl

-- A claimed positive pointwise lower bound must, when instantiated on this
-- exact pure-rotation jet, provide a strictly positive lower product while the
-- strain side is zero.  Keeping product positivity explicit makes the no-go
-- independent of a particular ordered-ring helper theorem.
record PositivePointwiseStrainVorticityLowerBound : Set where
  field
    lowerConstant : ℚ
    lowerConstantPositive : 0ℚ < lowerConstant
    pureRotationLowerProductPositive :
      0ℚ < lowerConstant * (1ℚ + 1ℚ)
    atPureRotationJet :
      lowerConstant * (1ℚ + 1ℚ) ≤ 0ℚ

open PositivePointwiseStrainVorticityLowerBound public

positivePointwiseLowerBoundImpossible :
  PositivePointwiseStrainVorticityLowerBound →
  0ℚ < 0ℚ
positivePointwiseLowerBoundImpossible lower =
  ℚP.<-≤-trans
    (pureRotationLowerProductPositive lower)
    (atPureRotationJet lower)

round79TraceFreeOrderingAloneForcesStrainGapComparableToVorticity : Bool
round79TraceFreeOrderingAloneForcesStrainGapComparableToVorticity = false

round79EigenframeInjectionNeedsIndependentGapControl : Bool
round79EigenframeInjectionNeedsIndependentGapControl = true

round79TraceFreeOrderingAloneForcesStrainGapComparableToVorticityIsFalse :
  round79TraceFreeOrderingAloneForcesStrainGapComparableToVorticity ≡ false
round79TraceFreeOrderingAloneForcesStrainGapComparableToVorticityIsFalse = refl
