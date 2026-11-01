module DASHI.Algebra.Quantum.DASHIQuantumComputationProgram where

open import DASHI.Core.Prelude

open import DASHI.Algebra.Quantum.DASHIQuantumBridge public
open import DASHI.Algebra.Quantum.DASHIHybridExecution public
open import DASHI.Algebra.Quantum.DASHIStructuredStateCompression public
open import DASHI.Algebra.Quantum.DASHIQuantumNormalForm public

import DASHI.Algebra.Quantum.FiniteQuantumRegister
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite
import DASHI.Algebra.Quantum.GeneralShor

------------------------------------------------------------------------
-- Four original research lanes, matching the DASHI quantum-computation
-- programme. The finite-register/QFT/general-Shor modules are integrated as
-- qualified dependencies without changing the existing programme record or
-- re-exporting projections that collide with the wave bridge.
------------------------------------------------------------------------

data QuantumResearchLane : Set where
  DASHIOnQuantumHardware : QuantumResearchLane
  DASHIClassicalQuantumEmulation : QuantumResearchLane
  DASHIClassicalQuantumBridge : QuantumResearchLane
  DASHIQuantumNormalFormAdvantage : QuantumResearchLane

record QuantumComputationProgramme : Set₂ where
  field
    descentSystem : StrictDescentSystem
    bridge : CertifiedQuantumBridge descentSystem
    hybrid : HybridExecution descentSystem bridge

    compressionModel : CompressionModel
    compression : CertifiedCompression compressionModel

    programModel : QuantumProgramModel
    normalizer : DASHINormalizer programModel

open QuantumComputationProgramme public

-- The master programme keeps reversible transport, contractive semantic
-- selection, structured classical emulation, and operational normalisation
-- distinct but composable. Each lane has its own falsifiable witness surface.
record QuantumProgrammeEvidence
    (P : QuantumComputationProgramme) : Set₂ where
  field
    bridgeRoundTrip :
      BridgeRoundTrip (descentSystem P) (bridge P)

    strictCompression :
      StrictCompressionWitness (compressionModel P) (compression P)

    observableAdequacy :
      ObservableAdequacy (compressionModel P)

    strictNormalFormGain :
      StrictNormalFormGain (programModel P) (normalizer P)

open QuantumProgrammeEvidence public

------------------------------------------------------------------------
-- Additional algorithmic lane inventory. Kept separate from
-- QuantumResearchLane so existing exhaustive consumers remain source-stable.
------------------------------------------------------------------------

data QuantumAlgorithmLane : Set where
  finiteComputationalRegisters : QuantumAlgorithmLane
  finiteQuantumFourierTransform : QuantumAlgorithmLane
  generalAbelianHiddenSubgroup : QuantumAlgorithmLane
  shorOrderFinding : QuantumAlgorithmLane
  shorFactoring : QuantumAlgorithmLane
  shorDiscreteLogarithm : QuantumAlgorithmLane
