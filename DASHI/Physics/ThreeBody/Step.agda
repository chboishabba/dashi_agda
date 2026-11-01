module DASHI.Physics.ThreeBody.Step where

open import DASHI.Physics.TOperator as TOp

------------------------------------------------------------------------
-- Three-body evolution surface.
--
-- This is an operator scaffold, not a closed-form solver.

record ThreeBodyStep
  (State : Set)
  : Set₁ where
  field
    operator : TOp.TOperator State

  step : State → State
  step = TOp.TOperator.T operator

open ThreeBodyStep public
