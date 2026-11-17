module DASHI.Physics.CondensedMatter.MATBGQTMResolutionKernelReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-BOUNDED QTM RESOLUTION-KERNEL REPLAY
--
-- Xiao et al. 2026 report an upper bound of ~10 meV on the energy resolution
-- and a remote-band momentum FWHM of ~0.03 nm^-1.  The numerical producer
-- turns those coordinates into normalized Gaussian kernels on a synthetic
-- delta-like fixture.  Gaussianity is a DASHI modelling choice here, not a
-- source-measured instrument-response function.
------------------------------------------------------------------------

record QTMResolutionKernelReceipt : Set where
  constructor qtm-resolution-kernel-receipt
  field
    sourceDOI : String
    producer : String
    evidence : String
    sourceEnergyFWHMUpperBoundMeV : String
    sourceMomentumFWHMInvNm : String
    gaussianEnergySigmaMeV : String
    gaussianMomentumSigmaInvNm : String
    energyKernelIntegral : String
    momentumKernelIntegral : String
    numericalReplayPaid : Bool
    gaussianResponseSourceMeasured : Bool
    experimentalIntensityArraysUsed : Bool
    interactingQTMFitPaid : Bool
    measuredQuantumMetricPaid : Bool

open QTMResolutionKernelReceipt public

canonicalQTMResolutionKernelReceipt : QTMResolutionKernelReceipt
canonicalQTMResolutionKernelReceipt =
  qtm-resolution-kernel-receipt
    "10.1038/s41586-026-10378-x"
    "scripts/matbg_qtm_resolution_kernel.py"
    "Docs/evidence/matbg_qtm_resolution_kernel_2026-10-16.json"
    "10"
    "0.03"
    "4.2466090014400955"
    "0.012739827004320286"
    "0.9999999999999999"
    "1.0000000000000002"
    true false false false false

record QTMResolutionKernelBoundary : Set where
  constructor qtm-resolution-kernel-boundary
  field
    sourceResolutionCoordinatesPaid : Bool
    normalizedSyntheticKernelExecuted : Bool
    gaussianModelDoesNotBecomeMeasuredInstrumentResponse : Bool
    resolutionReplayDoesNotCreateExperimentalIntensityArrays : Bool
    resolutionReplayDoesNotCreateInteractingQTMFit : Bool
    resolutionReplayDoesNotCreateMeasuredQuantumMetric : Bool

open QTMResolutionKernelBoundary public

canonicalQTMResolutionKernelBoundary : QTMResolutionKernelBoundary
canonicalQTMResolutionKernelBoundary =
  qtm-resolution-kernel-boundary true true true true true true
