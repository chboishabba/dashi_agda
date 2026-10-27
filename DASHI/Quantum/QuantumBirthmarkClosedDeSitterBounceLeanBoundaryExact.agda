{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkClosedDeSitterBounceLeanBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CROSS-KERNEL SOURCE RECEIPT
--
-- Lean owner: Synthesis/ClosedDeSitterBounce.lean
--
-- Source-written theorems on the same H=1 closed-slicing fixture:
--   scaleFactor(t) = cosh t
--   scaleVelocity(t) = sinh t
--   d/dt scaleFactor = scaleVelocity
--   d/dt scaleVelocity = scaleFactor
--   scaleVelocity^2 + 1 = scaleFactor^2
--   scaleFactor(0)=1, scaleVelocity(0)=0, scaleFactor(t)>=1.
--
-- This pays the differential real-analysis fixture.  It does not prove that
-- the history/CMP119 source selects that fixture.
------------------------------------------------------------------------

leanOwner : String
leanOwner = "Synthesis/ClosedDeSitterBounce.lean"

differentiableClosedDeSitterBounceSourceWritten : Bool
differentiableClosedDeSitterBounceSourceWritten = true

closedFriedmannSourceWritten : Bool
closedFriedmannSourceWritten = true

nonzeroRadiusBounceMinimumSourceWritten : Bool
nonzeroRadiusBounceMinimumSourceWritten = true

historySectorSelectionStillRequired : Bool
historySectorSelectionStillRequired = true

leanKernelReceiptClaimedInThisAgdaOwner : Bool
leanKernelReceiptClaimedInThisAgdaOwner = false
