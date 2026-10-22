module DASHI.Physics.QuantumSensors.DiamondMCGAxialResonanceBridgeExact where

-- End-to-end finite-mode current -> magnetic field -> axial NV labelled
-- transition model. This bridge does NOT derive optical fluorescence, a
-- stochastic likelihood, cardiac torso volume conduction or measured data.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_)
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.QuantumSensors.NVSpinOneAxialExact as NV
import DASHI.Physics.QuantumSensors.NVFiniteResonanceReadoutExact as Resonance
import DASHI.Physics.QuantumSensors.DiamondMCGFiniteBridgeExact as MCG

record FiniteNVMCGDevice : Set where
  constructor finite-nv-mcg-device
  field
    magneticForward : MCG.FiniteModeMCG
    zeroFieldSplitting : ℚ
    gyromagneticRatio : ℚ
    microwaveReference : ℚ
open FiniteNVMCGDevice public

deviceNV : FiniteNVMCGDevice → V.Vector3 → NV.AxialNV
deviceNV p j = NV.axial-nv
  (zeroFieldSplitting p)
  (gyromagneticRatio p)
  (MCG.modelMCG (magneticForward p) j)

deviceResonance : FiniteNVMCGDevice → V.Vector3 → Resonance.FiniteResonance
deviceResonance p j =
  Resonance.finite-resonance (deviceNV p j) (microwaveReference p)

predictedResonance :
  FiniteNVMCGDevice → V.Vector3 → Resonance.SymbolicODMRDatum
predictedResonance p j = Resonance.predictODMR (deviceResonance p j)

-- Exact finite Fourier-mode field to Zeeman splitting transport.
sourceToNVSplit :
  (p : FiniteNVMCGDevice) (j : V.Vector3) →
  NV.signedSplitting (deviceNV p j) ≡
  gyromagneticRatio p * MCG.modelMCG (magneticForward p) j +
  gyromagneticRatio p * MCG.modelMCG (magneticForward p) j
sourceToNVSplit p j = NV.axialSplittingIdentity (deviceNV p j)
