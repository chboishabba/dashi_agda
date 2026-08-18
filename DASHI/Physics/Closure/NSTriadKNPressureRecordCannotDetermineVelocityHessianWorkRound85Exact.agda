module DASHI.Physics.Closure.NSTriadKNPressureRecordCannotDetermineVelocityHessianWorkRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in the dynamics of intense velocity gradients in
-- turbulent flows".
-- Journal of Fluid Mechanics 973 (2023), A23.
-- DOI: 10.1017/jfm.2023.786.
--
-- Authors: Jinhee Jeong; Fazle Hussain.
-- Title: "On the identification of a vortex".
-- Journal of Fluid Mechanics 285 (1995), 69--94.
-- DOI: 10.1017/S0022112095000462.
--
-- ROUND85 / THE ROUND78--79 PRESSURE RECORD IS NOT YET A C4 OBSERVER
--
-- The exact pressure-relative-growth decomposition exposes a selected
-- velocity--Hessian bilinear.  Round78--79 currently retain pressure through:
--
--   * trace(H), equivalently Q through Delta p = 2Q;
--   * the vorticity contraction omega^T H omega;
--   * selected off-diagonal eigenframe injection.
--
-- These observables do NOT determine an arbitrary velocity--Hessian bilinear.
-- The exact rational witness is
--
--   H0 = 0,
--   H1 = diag(1,0,-1),
--   omega = e2,
--   injection coordinate = e3^T H e2,
--   velocity test = e1^T H e1.
--
-- Both Hessians have
--
--   trace = 0,
--   e2^T H e2 = 0,
--   e3^T H e2 = 0,
--
-- but the selected velocity work is 0 for H0 and 1 for H1.
--
-- Therefore C4 cannot consume the old pressure record by semantic relabelling.
-- A sufficient bridge must additionally control the selected velocity--Hessian
-- work itself or retain a stronger norm-level Hessian quantity from which that
-- work is quantitatively bounded.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as A
import DASHI.Physics.Closure.NSTriadKNPressureContractionInjectionSeparationRound79Exact as R79

basisE1 : V.Vector3
basisE1 = V.v3 1ℚ 0ℚ 0ℚ

basisE2 : V.Vector3
basisE2 = V.v3 0ℚ 1ℚ 0ℚ

basisE3 : V.Vector3
basisE3 = V.v3 0ℚ 0ℚ 1ℚ

zeroHessian : M.Matrix3
zeroHessian = M.zeroMatrix

traceFreeDiagonalHessian : M.Matrix3
traceFreeDiagonalHessian = M.matrix3
  1ℚ 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ
  0ℚ 0ℚ (- 1ℚ)

matrixTrace : M.Matrix3 → ℚ
matrixTrace H = M.m11 H + M.m22 H + M.m33 H

vorticityContraction : M.Matrix3 → ℚ
vorticityContraction H = V.dot basisE2 (A.apply H basisE2)

frameInjection23 : M.Matrix3 → ℚ
frameInjection23 H = V.dot basisE3 (A.apply H basisE2)

velocityHessianWork11 : M.Matrix3 → ℚ
velocityHessianWork11 H = V.dot basisE1 (A.apply H basisE1)

zeroTrace0 : matrixTrace zeroHessian ≡ 0ℚ
zeroTrace0 = solve []

zeroTrace1 : matrixTrace traceFreeDiagonalHessian ≡ 0ℚ
zeroTrace1 = solve []

sameTrace : matrixTrace zeroHessian ≡ matrixTrace traceFreeDiagonalHessian
sameTrace = trans zeroTrace0 (sym zeroTrace1)

zeroVorticityContraction0 : vorticityContraction zeroHessian ≡ 0ℚ
zeroVorticityContraction0 = solve []

zeroVorticityContraction1 :
  vorticityContraction traceFreeDiagonalHessian ≡ 0ℚ
zeroVorticityContraction1 = solve []

sameVorticityContraction :
  vorticityContraction zeroHessian
  ≡ vorticityContraction traceFreeDiagonalHessian
sameVorticityContraction =
  trans zeroVorticityContraction0 (sym zeroVorticityContraction1)

zeroFrameInjection0 : frameInjection23 zeroHessian ≡ 0ℚ
zeroFrameInjection0 = solve []

zeroFrameInjection1 : frameInjection23 traceFreeDiagonalHessian ≡ 0ℚ
zeroFrameInjection1 = solve []

sameFrameInjection :
  frameInjection23 zeroHessian ≡ frameInjection23 traceFreeDiagonalHessian
sameFrameInjection = trans zeroFrameInjection0 (sym zeroFrameInjection1)

zeroVelocityWork : velocityHessianWork11 zeroHessian ≡ 0ℚ
zeroVelocityWork = solve []

unitVelocityWork : velocityHessianWork11 traceFreeDiagonalHessian ≡ 1ℚ
unitVelocityWork = solve []

record PressureRecordDeterminesVelocityHessianWork : Set where
  field
    determine :
      (left right : M.Matrix3) →
      matrixTrace left ≡ matrixTrace right →
      vorticityContraction left ≡ vorticityContraction right →
      frameInjection23 left ≡ frameInjection23 right →
      velocityHessianWork11 left ≡ velocityHessianWork11 right

open PressureRecordDeterminesVelocityHessianWork public

pressureRecordCannotDetermineVelocityHessianWork :
  PressureRecordDeterminesVelocityHessianWork → 0ℚ ≡ 1ℚ
pressureRecordCannotDetermineVelocityHessianWork candidate =
  let
    workEqual = determine candidate
      zeroHessian traceFreeDiagonalHessian
      sameTrace sameVorticityContraction sameFrameInjection
  in
  trans (sym zeroVelocityWork) (trans workEqual unitVelocityWork)

-- The older Round79 theorem remains a distinct incomparability result: its
-- witness varies off-diagonal injection at fixed vorticity contraction.  The
-- present witness varies velocity-Hessian work while fixing BOTH quantities
-- and the trace/Q coordinate.
round85ExtendsRound79PressureObserverNoGo : Bool
round85ExtendsRound79PressureObserverNoGo =
  R79.round79C3MustCarryStretchingAndRotationPressureObservables

round85TraceQContractionInjectionDetermineVelocityHessianWork : Bool
round85TraceQContractionInjectionDetermineVelocityHessianWork = false

round85C4NeedsSelectedVelocityHessianOrStrongerNormBudget : Bool
round85C4NeedsSelectedVelocityHessianOrStrongerNormBudget = true

round85TraceQContractionInjectionDetermineVelocityHessianWorkIsFalse :
  round85TraceQContractionInjectionDetermineVelocityHessianWork ≡ false
round85TraceQContractionInjectionDetermineVelocityHessianWorkIsFalse = refl
