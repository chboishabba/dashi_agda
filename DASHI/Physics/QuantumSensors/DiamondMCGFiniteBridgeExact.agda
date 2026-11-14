module DASHI.Physics.QuantumSensors.DiamondMCGFiniteBridgeExact where

-- A finite-mode bridge to the existing exact Maxwell / Fourier Biot-Savart
-- carrier. Magnetic readout is only a projection; calibrated diamond optical
-- physics, tissue conductivity and continuum cardiac transfer remain open.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNMaxwellFluidBiotSavartBridgeExact as EM
import DASHI.Physics.Measurement.CausalBioelectromagneticExperimentExact as C

record FiniteModeMCG : Set where
  constructor finite-mode-mcg
  field
    coupling : ℚ
    modeData : V.ProjectionMode
    sensorAxis : V.Vector3
open FiniteModeMCG public

-- Current and field in the same rational Fourier mode; not a torso integral.
cardiacModeToField : FiniteModeMCG → V.Vector3 → V.Vector3
cardiacModeToField p =
  EM.magneticFieldFromCurrent (coupling p) (modeData p)

-- A scalar sensor-axis readout is the relevant observable coordinate.
axialField : FiniteModeMCG → V.Vector3 → ℚ
axialField p b = V.dot (sensorAxis p) b

modelMCG : FiniteModeMCG → V.Vector3 → ℚ
modelMCG p j = axialField p (cardiacModeToField p j)

finiteModeForward :
  (p : FiniteModeMCG) →
  C.BioEMForward V.Vector3 V.Vector3 V.Vector3
finiteModeForward p = record
  { currentFromIntervention = λ j → j
  ; fieldFromCurrent = cardiacModeToField p
  }

finiteModeReadout :
  (p : FiniteModeMCG) →
  C.MagneticReadout V.Vector3 ℚ
finiteModeReadout p = record { observation = axialField p }

finiteMCGComposition :
  (p : FiniteModeMCG) (j : V.Vector3) →
  C.predictedDatum (finiteModeForward p) (finiteModeReadout p) j
  ≡ modelMCG p j
finiteMCGComposition p j = refl

-- Only established after adding a source-backed optical calibration receipt:
-- MCG spectral/fluorescence measurement; heartbeat filtering; noise bounds;
-- source location, volume conduction and geometric reconstruction.
