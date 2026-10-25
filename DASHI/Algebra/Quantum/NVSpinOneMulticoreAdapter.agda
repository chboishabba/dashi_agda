module DASHI.Algebra.Quantum.NVSpinOneMulticoreAdapter where

-- A hardware-specific *structural* adapter. All underlying spin and
-- quantum computation objects live in existing modules.
-- No new spin-1 axioms, physical fidelity assumptions, or device claims.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import DASHI.Physics.QFT.NonAbelianFusionFromSpin
  using (SpinIrrep; spin-one; spinIrrepDimension)
import DASHI.Algebra.Quantum.DASHIQuantumBridge as Bridge
import DASHI.Algebra.Quantum.DASHIQuantumComputationProgram as Programme

-- The pre-existing SU(2) spin-one representation has dimension three.
nvElectronCarrierDimension : Nat
nvElectronCarrierDimension = spinIrrepDimension spin-one

nvElectronCarrierDimensionIsThree :
  nvElectronCarrierDimension ≡ 3
nvElectronCarrierDimensionIsThree = refl

-- A topology *candidate* motivated by a 16 x 8 multicore description.
-- Connectivity inside each core and inter-core entanglement are NOT inferred.
Core : Set
Core = Fin 16

Site : Set
Site = Fin 8

record Address : Set where
  constructor address
  field
    core : Core
    site : Site

open Address public

-- Only local gates are admitted here. A multi-core quantum gate must be
-- introduced by a separate explicitly evidenced hardware resource.
data LocalGate : Set where
  single : (a : Address) -> LocalGate
  pairWithinCore : (c : Core) -> (s t : Site) -> LocalGate

-- A well-formed local pair carries its shared core in its constructor;
-- no proof-irrelevant assertion of remote quantum connectivity is smuggled in.
pairEndpoints : (c : Core) -> (s t : Site) -> Address -> Address
pairEndpoints c s t = address c s

-- Device execution is a refinement of the EXISTING certified bridge,
-- not a replacement quantum formalism.
record NVBridgeAdapter (D : Bridge.StrictDescentSystem)
                       (B : Bridge.CertifiedQuantumBridge D) : Set₁ where
  field
    compileLocal : LocalGate -> Bridge.Wave B -> Bridge.Wave B
    -- Unitarity and physical gate availability are evidence obligations
    -- for a populated instance, not claimed by this structural module.

-- Source boundary:
-- (1) spin-one carrier and quantum bridge are prior in-repository work;
-- (2) 16 x 8 is a vendor-architecture assumption, not independently proved;
-- (3) a physically implemented cross-core entangler requires a new witness;
-- (4) nothing here proves readout fidelity, entanglement or hardware advantage.
