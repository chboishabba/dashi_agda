module DASHI.Physics.Optics.BerkeleyDiffuserCamSourceOperatorExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.BerkeleyDiffuserCamPublicCalibrationExact as Calibration
import DASHI.Physics.Optics.DiffuserPhysicalForwardWeldExact as Weld

------------------------------------------------------------------------
-- SOURCE-CODE OPERATOR RECEIPT
--
-- DiffuserCam_main.m loads the pinned PSF stack, subtracts the PSF bias,
-- optionally averages lateral/axial blocks, resizes and normalises the camera
-- measurement, then calls ADMM3D_solver.m. The solver flips/shifts the depth
-- stack, normalises it, computes its 3-D FFT, applies the forward/adjoint via
-- FFT multiplication, enforces a nonnegative primal projection, and supports
-- 3-D TV and native sparsity regularisation. These are source semantics, not a
-- decoded matrix H or a proof of the optical propagation law.
------------------------------------------------------------------------

sourceMainBlobSHA : String
sourceMainBlobSHA = "a05211789d363b1b770110bd71013a1b7564e901"

sourceSolverBlobSHA : String
sourceSolverBlobSHA = "0168cc8a6b40123baaba4120b6c594375659c4d6"

sourceSettingsBlobSHA : String
sourceSettingsBlobSHA = "a495b77703e32b7696565f0d9f8e23f00439ad03"

psfBias : Nat
psfBias = 102

imageBias : Nat
imageBias = 100

sourceForwardUsesFFTConvolution : Bool
sourceForwardUsesFFTConvolution = true

sourceAdjointUsesConjugateSpectrum : Bool
sourceAdjointUsesConjugateSpectrum = true

sourceUsesDepthFlipAndShift : Bool
sourceUsesDepthFlipAndShift = true

sourceNormalisesPSFStack : Bool
sourceNormalisesPSFStack = true

sourceUsesThreeDimensionalTV : Bool
sourceUsesThreeDimensionalTV = true

sourceUsesNonnegativeProjection : Bool
sourceUsesNonnegativeProjection = true

sourceSupportsNativeSparsity : Bool
sourceSupportsNativeSparsity = true

-- Exact numerical materialisation of the binary PSF stack is still required
-- before singular values, coherence, or a same-H condition number can be
-- computed in this tranche.
numericOperatorMatrixMaterialised : Bool
numericOperatorMatrixMaterialised = false

record BerkeleyDiffuserCamSourceOperatorReceipt : Set where
  field
    calibrationCommit : String
    mainBlob : String
    solverBlob : String
    settingsBlob : String
    psfSensorBias : Nat
    measurementSensorBias : Nat
    fftConvolution : Bool
    conjugateSpectrumAdjoint : Bool
    depthFlipAndShift : Bool
    psfNormalisation : Bool
    threeDimensionalTV : Bool
    nonnegativeProjection : Bool
    nativeSparsity : Bool
    literalNumericHMaterialised : Bool

open BerkeleyDiffuserCamSourceOperatorReceipt public

publicDiffuserCamSourceOperatorReceipt : BerkeleyDiffuserCamSourceOperatorReceipt
publicDiffuserCamSourceOperatorReceipt = record
  { calibrationCommit = Calibration.diffuserCamCommit
  ; mainBlob = sourceMainBlobSHA
  ; solverBlob = sourceSolverBlobSHA
  ; settingsBlob = sourceSettingsBlobSHA
  ; psfSensorBias = psfBias
  ; measurementSensorBias = imageBias
  ; fftConvolution = sourceForwardUsesFFTConvolution
  ; conjugateSpectrumAdjoint = sourceAdjointUsesConjugateSpectrum
  ; depthFlipAndShift = sourceUsesDepthFlipAndShift
  ; psfNormalisation = sourceNormalisesPSFStack
  ; threeDimensionalTV = sourceUsesThreeDimensionalTV
  ; nonnegativeProjection = sourceUsesNonnegativeProjection
  ; nativeSparsity = sourceSupportsNativeSparsity
  ; literalNumericHMaterialised = numericOperatorMatrixMaterialised
  }

-- Importing Weld ensures this source owner sits on the same physical-forward
-- seam; no constructor here claims that source-code provenance alone inhabits
-- Weld.PhysicalDiffuserForwardWeld for the actual instrument.
