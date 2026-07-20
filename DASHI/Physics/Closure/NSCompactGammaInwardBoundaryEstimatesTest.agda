module DASHI.Physics.Closure.NSCompactGammaInwardBoundaryEstimatesTest where

open import DASHI.Physics.Closure.NSCompactGammaInwardBoundaryEstimates

------------------------------------------------------------------------
-- Focused import regression: the theorem-facing A1--A12 names remain
-- available from one canonical module without strengthening analytic leaves.
------------------------------------------------------------------------

A1 = A1-continuity-along-selected-path
A2 = A2-dini-derivatives-available
A3 = A3-near-replenishment-lower-bound
A4 = A4-inward-packet-energy-derivative
A5 = A5-near-shell-boundary-gain
A6 = A6-absorbed-far-tail-estimate
A7 = A7-strict-inward-compact-gamma-boundary
A8 = A8-accumulated-loss-bound
A9 = A9-sufficient-initial-reserve
A10 = A10-X-norm-inward-estimate
A11 = A11-inward-off-packet-derivative
A12 = A12-compact-gamma-invariant-region

uniformGalerkin = uniform-boundary-certificate-gives-preservation
continuumClosedness = closed-inward-region-passes-to-continuum
