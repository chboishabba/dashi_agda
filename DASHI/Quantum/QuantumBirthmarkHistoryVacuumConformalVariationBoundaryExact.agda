{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHistoryVacuumConformalVariationBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CROSS-KERNEL SOURCE RECEIPT
--
-- Lean owner: Synthesis/HistoryVacuumConformalVariation.lean
--
-- For the explicit four-dimensional conformal variation g -> exp(2s) g,
-- the selected model action is
--
--   S_vac(s) = -lambda exp(4s).
--
-- Lean source proves
--   dS_vac/ds = -4 lambda exp(4s),
-- hence at s=0 positive lambda gives a negative trace coordinate -4 lambda.
-- The finite birthmark-model amplitudes produce exact traces
--   lambda=21/64 -> -21/16,
--   lambda=3/8   -> -3/2.
--
-- This closes the MODEL metric-variation sign.  It does not manufacture the
-- CMP119 Eq.(2.23) vacuumMetricVariation callback, whose source record remains
-- unconstrained and therefore requires a source-native metric-variation theorem.
------------------------------------------------------------------------

leanOwner : String
leanOwner = "Synthesis/HistoryVacuumConformalVariation.lean"

modelConformalMetricVariationSignSourceWritten : Bool
modelConformalMetricVariationSignSourceWritten = true

positiveAmplitudeGivesNegativeTraceSourceWritten : Bool
positiveAmplitudeGivesNegativeTraceSourceWritten = true

lowAndHighFiniteBirthmarkTraceValuesSourceWritten : Bool
lowAndHighFiniteBirthmarkTraceValuesSourceWritten = true

cmp119SourceNativeMetricVariationStillRequired : Bool
cmp119SourceNativeMetricVariationStillRequired = true

modelSignDoesNotPromoteCMP119SourceSign : Bool
modelSignDoesNotPromoteCMP119SourceSign = true

leanKernelReceiptClaimedInThisAgdaOwner : Bool
leanKernelReceiptClaimedInThisAgdaOwner = false
