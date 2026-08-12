module DASHI.Foundations.DepthWheelStroboscopicContractionExact where

------------------------------------------------------------------------
-- CONCRETE STROBOSCOPIC DEPTH-WHEEL CONTRACTION
--
-- The address wheel elsewhere in the repository is an ultrametric isometry.
-- This module answers the distinct depth-evolution question with one honest
-- concrete system.  On Base369State, phase 0 and phase 1 preserve state while
-- phase 2 applies the already-proved strict Base369 contraction kernel.
-- Therefore one full depth wheel is definitionally that kernel and inherits
-- its contraction certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; pred)

import DASHI.Core.Base369UltrametricContraction as Base
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

identity : Base.Base369State → Base.Base369State
identity x = x

contractingDepthWheel : Wheel.DepthWheelSystem Base.Base369State
contractingDepthWheel =
  Wheel.depthWheelSystem
    identity
    identity
    Base.base369Kernel

oneWheelIsBaseKernel :
  (state : Base.Base369State) →
  Wheel.oneWheelRenormalisation contractingDepthWheel state
  ≡ Base.base369Kernel state
oneWheelIsBaseKernel state = refl

oneWheelStrictlyContracts :
  (left right : Base.Base369State) →
  Base.base369Distance
    (Wheel.oneWheelRenormalisation contractingDepthWheel left)
    (Wheel.oneWheelRenormalisation contractingDepthWheel right)
  ≤ pred (Base.base369Distance left right)
oneWheelStrictlyContracts left right =
  Base.base369Kernel-contractive left right

------------------------------------------------------------------------
-- Stroboscopic orbit sampled only at wheel-normal sections n = 3q.
------------------------------------------------------------------------

stroboscopicState : Nat → Base.Base369State → Base.Base369State
stroboscopicState zero initial = initial
stroboscopicState (suc q) initial =
  Wheel.oneWheelRenormalisation contractingDepthWheel
    (stroboscopicState q initial)

stroboscopicRecurrence :
  (q : Nat) → (initial : Base.Base369State) →
  stroboscopicState (suc q) initial
  ≡
  Wheel.oneWheelRenormalisation contractingDepthWheel
    (stroboscopicState q initial)
stroboscopicRecurrence q initial = refl

stroboscopicStepContracts :
  (q : Nat) →
  (left right : Base.Base369State) →
  Base.base369Distance
    (stroboscopicState (suc q) left)
    (stroboscopicState (suc q) right)
  ≤
  pred
    (Base.base369Distance
      (stroboscopicState q left)
      (stroboscopicState q right))
stroboscopicStepContracts q left right =
  Base.base369Kernel-contractive
    (stroboscopicState q left)
    (stroboscopicState q right)

------------------------------------------------------------------------
-- Boundary: this proves existence of a genuinely contractive depth-wheel
-- system.  It does not claim every phase-dependent wheel contracts, and it
-- does not alter the separate theorem that the p7 address rotation is an
-- isometry.
------------------------------------------------------------------------
