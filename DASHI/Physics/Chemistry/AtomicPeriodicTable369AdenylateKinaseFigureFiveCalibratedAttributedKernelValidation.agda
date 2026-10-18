module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFiveCalibratedAttributedKernelValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFiveCalibratedAttributedKernelExact as Kernel

-- Regression surface: the exact Figure-5 numeric acquisition must be connected
-- to the existing attributed sparse kernel rather than living only in a ledger.

calibratedKernel = Kernel.canonicalFigureFiveCalibratedAttributedKernel
calibratedRouteEdges = Kernel.calibratedRouteEdges
figureFiveStateEnergies = Kernel.figureFiveStateEnergies
figureFiveDirectedRates = Kernel.figureFiveDirectedRates
calibratedKernelBoundary = Kernel.canonicalFigureFiveCalibratedAttributedKernelBoundary
