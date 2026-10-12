module DASHI.Physics.Optics.WallerDiffuserCamCodeForwardExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

-- Literal code-facing receipt for the pinned public Waller Lab solver.
-- The names below mirror implementation semantics at commit
-- c8516cb8f482c2bb15e75ebebd91a74b88732c95 without copying the MATLAB source.

wallerSolverCommit : String
wallerSolverCommit = "c8516cb8f482c2bb15e75ebebd91a74b88732c95"

psfBias102 : Nat
psfBias102 = 102

imageBias100 : Nat
imageBias100 = 100

record WallerDiffuserCamCodeForwardReceipt : Set where
  field
    measuredPSFStackLoaded : Bool
    psfBiasSubtractedBeforeForwardBuild : Bool
    imageBiasSubtractedBeforeNormalisation : Bool
    fftConvolutionForward : Bool
    fftConvolutionAdjoint : Bool
    forwardAndAdjointShareOneSpectrum : Bool
    nonnegativeReconstruction : Bool
    tvRegularisationAvailable : Bool
    nativeSparsityAvailable : Bool
    threeDimensionalADMM : Bool
    sourceCodeDerivesPhysicalDiffractionLaw : Bool
    solverSuccessProvesGlobalInjectivity : Bool

open WallerDiffuserCamCodeForwardReceipt public

wallerDiffuserCamCodeForwardReceipt : WallerDiffuserCamCodeForwardReceipt
wallerDiffuserCamCodeForwardReceipt = record
  { measuredPSFStackLoaded = true
  ; psfBiasSubtractedBeforeForwardBuild = true
  ; imageBiasSubtractedBeforeNormalisation = true
  ; fftConvolutionForward = true
  ; fftConvolutionAdjoint = true
  ; forwardAndAdjointShareOneSpectrum = true
  ; nonnegativeReconstruction = true
  ; tvRegularisationAvailable = true
  ; nativeSparsityAvailable = true
  ; threeDimensionalADMM = true
  ; sourceCodeDerivesPhysicalDiffractionLaw = false
  ; solverSuccessProvesGlobalInjectivity = false
  }
