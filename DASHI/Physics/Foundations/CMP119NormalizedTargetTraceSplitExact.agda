{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119NormalizedTargetTraceSplitExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

------------------------------------------------------------------------
-- EXACT TRACE / TRACELESS SPLIT OF THE NORMALIZED TARGET
--
-- Target diagonal:
--   (1,-1,-1,-1)
--
-- Sum = -2.  Its isotropic trace part is therefore (-1/2) on each diagonal,
-- and the remaining traceless part is
--   (3/2,-1/2,-1/2,-1/2).
--
-- This does not assert the physical origin of the trace part.  It proves the
-- amount any nonclassical/quantum contribution must supply if the classical
-- contribution remains traceless.
------------------------------------------------------------------------

target00 target11 target22 target33 : ℚ
target00 = + 1 / 1
target11 = - (+ 1 / 1)
target22 = - (+ 1 / 1)
target33 = - (+ 1 / 1)

targetTrace : ℚ
targetTrace = target00 + target11 + target22 + target33

targetTraceIsNegativeTwo :
  targetTrace ≡ - (+ 2 / 1)
targetTraceIsNegativeTwo = ℚRing.solve []

isotropicTracePart : ℚ
isotropicTracePart = - (+ 1 / 2)

traceless00 traceless11 traceless22 traceless33 : ℚ
traceless00 = + 3 / 2
traceless11 = - (+ 1 / 2)
traceless22 = - (+ 1 / 2)
traceless33 = - (+ 1 / 2)

target00Split :
  target00 ≡ traceless00 + isotropicTracePart
target00Split = ℚRing.solve []

target11Split :
  target11 ≡ traceless11 + isotropicTracePart
target11Split = ℚRing.solve []

target22Split :
  target22 ≡ traceless22 + isotropicTracePart
target22Split = ℚRing.solve []

target33Split :
  target33 ≡ traceless33 + isotropicTracePart
target33Split = ℚRing.solve []

tracelessPartTraceIsZero :
  traceless00 + traceless11 + traceless22 + traceless33
  ≡ + 0 / 1
tracelessPartTraceIsZero = ℚRing.solve []

fourIsotropicPartsGiveTargetTrace :
  isotropicTracePart + isotropicTracePart
  + isotropicTracePart + isotropicTracePart
  ≡ targetTrace
fourIsotropicPartsGiveTargetTrace = ℚRing.solve []
