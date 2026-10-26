module DASHI.Physics.QuantumSensors.NVReadoutRegisterBoundaryExact where

-- A finite carrier distinction for the parallel SAXON Q architecture audit:
-- electronic NV sensor m_s labels and a candidate nuclear logical register
-- are DIFFERENT typed domains. This does not assume the manufacturer's
-- actual isotope, register encoding, or pulse mapping.
--
-- Mathematical implementation: DASHI, 2026-10-26.
-- Original physical source ownership remains in Diamond MCG #1238.
-- SAXON Q source intake and logical candidate owner: Agda #1270.
-- No hardware identification or experimental evidence is imported.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3

data Register : Set where
  electronSensor nuclearMemory : Register

-- Indexed levels deliberately cannot be transported between registers
-- without a separately supplied physical encoding/measurement map.
data Level : Register → Set where
  ePlus eZero eMinus : Level electronSensor
  nZero nOne : Level nuclearMemory

electronLevelChart : C3.C3 → Level electronSensor
electronLevelChart C3.c0 = ePlus
electronLevelChart C3.c1 = eZero
electronLevelChart C3.c2 = eMinus

-- The existing zero-field energy collision concerns electronic ±1:
-- it does NOT imply a collision between two nuclear logical values.
-- Neither does photon contrast of electron levels automatically imply
-- any nuclear-memory readout, nuclear coherence or gate fidelity.

record ReadoutAdapter : Set₁ where
  field
    prepare : Level nuclearMemory → Level electronSensor
    -- A proposed source-to-sensor encoding must be a user-supplied
    -- experiment-specific object; no canonical construction is given.

-- A formal adapter alone is not an experimentally verified control pulse,
-- nor a quantum channel on density operators. The above is intentionally
-- a first-order basis interface and cannot establish actual readout.
