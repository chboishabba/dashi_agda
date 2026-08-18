module DASHI.Physics.Closure.NSTriadKNPressureContractionInjectionSeparationRound79Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in the dynamics of intense velocity gradients in
-- turbulent flows".
-- Journal of Fluid Mechanics 973 (2023), A23.
-- DOI: 10.1017/jfm.2023.786.
--
-- Authors: Wm. T. Ashurst; A. R. Kerstein; R. M. Kerr; C. H. Gibson.
-- Title: "Alignment of vorticity and scalar gradient with strain rate in
-- simulated Navier-Stokes turbulence".
-- DOI: 10.1063/1.866513.
--
-- Author: Andrea Cavazzini.
-- Title: "Self-Frustration of Vortex Stretching and the Architecture of the
-- Navier-Stokes Blow-Up Barrier".
-- DOI: 10.5281/zenodo.19158797.
--
-- ROUND79 / TWO PRESSURE OBSERVABLES ARE NECESSARY
--
-- Round78 reduced the stretching-amplitude side to the scalar contraction
--
--   omega^T H omega.
--
-- The pre-existing eigenframe/coherence lane, however, evolves strain
-- eigenvectors through OFF-DIAGONAL pressure-Hessian entries divided by a
-- strain spectral gap. These are different observables.
--
-- This file gives an exact rational counterexample: two symmetric pressure
-- Hessians have the SAME contraction along omega=e2 but DIFFERENT e2->e3
-- injection. Therefore a bound on omega^T H omega alone cannot close the
-- eigenframe-rotation/depletion branch. C3 must carry both:
--
--   (1) pressure contraction / stretching acceleration;
--   (2) off-diagonal pressure injection together with its actual gap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as A

basisE2 basisE3 : V.Vector3
basisE2 = V.v3 0ℚ 1ℚ 0ℚ
basisE3 = V.v3 0ℚ 0ℚ 1ℚ

zeroPressure : M.Matrix3
zeroPressure = M.zeroMatrix

mixedPressure : M.Matrix3
mixedPressure = M.matrix3
  0ℚ 0ℚ 0ℚ
  0ℚ 0ℚ 1ℚ
  0ℚ 1ℚ 0ℚ

pressureContraction : M.Matrix3 → V.Vector3 → ℚ
pressureContraction pressure omega =
  V.dot omega (A.apply pressure omega)

frameInjection23 : M.Matrix3 → ℚ
frameInjection23 pressure =
  V.dot basisE3 (A.apply pressure basisE2)

zeroPressureContraction :
  pressureContraction zeroPressure basisE2 ≡ 0ℚ
zeroPressureContraction = solve []

mixedPressureContraction :
  pressureContraction mixedPressure basisE2 ≡ 0ℚ
mixedPressureContraction = solve []

sameStretchingContraction :
  pressureContraction zeroPressure basisE2
  ≡ pressureContraction mixedPressure basisE2
sameStretchingContraction = refl

zeroFrameInjection : frameInjection23 zeroPressure ≡ 0ℚ
zeroFrameInjection = solve []

mixedFrameInjection : frameInjection23 mixedPressure ≡ 1ℚ
mixedFrameInjection = solve []

record PressureContractionDeterminesInjection : Set where
  field
    determine :
      (left right : M.Matrix3) →
      pressureContraction left basisE2 ≡ pressureContraction right basisE2 →
      frameInjection23 left ≡ frameInjection23 right

open PressureContractionDeterminesInjection public

pressureContractionCannotDetermineInjection :
  PressureContractionDeterminesInjection →
  0ℚ ≡ 1ℚ
pressureContractionCannotDetermineInjection candidate =
  let equalInjection =
        determine candidate zeroPressure mixedPressure sameStretchingContraction
  in
  equalInjection

round79PressureContractionDeterminesEigenframeInjection : Bool
round79PressureContractionDeterminesEigenframeInjection = false

round79C3MustCarryStretchingAndRotationPressureObservables : Bool
round79C3MustCarryStretchingAndRotationPressureObservables = true

round79PressureContractionDeterminesEigenframeInjectionIsFalse :
  round79PressureContractionDeterminesEigenframeInjection ≡ false
round79PressureContractionDeterminesEigenframeInjectionIsFalse = refl
