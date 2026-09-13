module DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyReferenceKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopySourceReplayExact as M

data MessengerTag : Set where
  nitrogenTag methaneTag : MessengerTag

optimalTagTemperature : MessengerTag → Nat
optimalTagTemperature nitrogenTag =
  M.MaiwaldValineSourceReplay.n2OptimalTagTemperatureK M.sourceExactMaiwaldValineReplay
optimalTagTemperature methaneTag =
  M.MaiwaldValineSourceReplay.ch4OptimalTagTemperatureK M.sourceExactMaiwaldValineReplay

record SpectralReferenceKernel : Set where
  constructor spectral-reference-kernel
  field
    lowerWavenumberCmInv : Nat
    upperWavenumberCmInv : Nat
    highlightedFeatureCmInv : Nat
    nitrogenOptimalK : Nat
    methaneOptimalK : Nat
    structuralInference : String
    exactIntensityArrayAvailable : Bool

open SpectralReferenceKernel public

maiwaldSpectralReferenceKernel : SpectralReferenceKernel
maiwaldSpectralReferenceKernel = spectral-reference-kernel
  (M.MaiwaldValineSourceReplay.lowerWavenumberCmInv M.sourceExactMaiwaldValineReplay)
  (M.MaiwaldValineSourceReplay.upperWavenumberCmInv M.sourceExactMaiwaldValineReplay)
  (M.MaiwaldValineSourceReplay.highlightedFeatureCmInv M.sourceExactMaiwaldValineReplay)
  (optimalTagTemperature nitrogenTag)
  (optimalTagTemperature methaneTag)
  (M.MaiwaldValineSourceReplay.structuralInference M.sourceExactMaiwaldValineReplay)
  false

referenceKernelReproducesSourceIntensitySpectrum : Bool
referenceKernelReproducesSourceIntensitySpectrum = false

referenceKernelCanSelectSourceTagTemperature : Bool
referenceKernelCanSelectSourceTagTemperature = true

nextExecutableLeaf : String
nextExecutableLeaf =
  "recover source spectral intensities, calibration axis, dissociation timing and tag-specific response arrays before replaying the measured action spectrum"
