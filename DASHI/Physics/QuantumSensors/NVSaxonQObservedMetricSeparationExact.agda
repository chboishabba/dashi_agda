module DASHI.Physics.QuantumSensors.NVSaxonQObservedMetricSeparationExact where

-- Source-specific *claim typing*, not reproduction of measured apparatus.
-- PRIMARY EXPERIMENT: S. Gemsheim et al., "Grover Search with Semiconductor
-- Spin Qubits at Ambient Conditions", arXiv:2609.13022 (2026).
-- The paper's reported Grover search success is distinct from separately
-- reported calibrated gate fidelities.
-- MANUFACTURER: SAXON Q SXQ128/SXQ512 multicore marketing (August 2026).
-- DASHI adaptation: 2026-10-26. No priority claimed for experimental results.
--
-- These data are author-reported decimal rational central values and
-- uncertainty magnitudes, NOT independent remeasurement or confidence bounds.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
import DASHI.Physics.QuantumSensors.NVSIMetrologyReadoutAdapterExact as SIAdapter

data MetricKind : Set where
  algorithmSuccess gateFidelity photonReadoutFidelity
  magneticSensitivity : MetricKind

record ReportedFraction (kind : MetricKind) : Set where
  constructor reported-fraction
  field
    central : ℚ
    reportedUncertainty : ℚ
open ReportedFraction public

-- Only appropriate percentages share this type. Physical sensitivity has
-- dimensions pT/sqrt(Hz); it is not a fraction or a Bernoulli probability.
record ReportedSensitivity : Set₁ where
  field
    instrument : SIAdapter.NVSIReadoutCalibration
    sourceIdentity : Set
    sourceReceipt : sourceIdentity

data ExperimentalRegister : Set where
  threeNuclearQubits aggregateMulticoreClaim : ExperimentalRegister

record ObservationClaim (register : ExperimentalRegister) : Set₁ where
  field
    sourceLocator : Set
    sourceWitness : sourceLocator
    metric : ReportedFraction algorithmSuccess

-- A method demanding experimental algorithm success cannot consume the
-- different-typed gate-fidelity or MCG sensitivity claim by accident.
acceptSearch : ReportedFraction algorithmSuccess →
               ReportedFraction algorithmSuccess
acceptSearch x = x

-- Source-only reference for explicit numerical transcription:
-- 77.3 +/- 3.4 percent, 87.0 +/- 4.2 percent in the primary preprint.
-- No numerical transcriptions are instantiated here, avoiding any
-- assumption about which published gate-fidelity figure refers to which
-- calibrated primitive or experiment revision.
