module DASHI.Algebra.Quantum.SaxonQConsumerRelativeFineBoundaryExact where

-- Cross-pollination from the repository's existing jCoarse/jFine
-- consumer-relative reduction, NOT an identification of NV qubits
-- with the modular j-invariant or its 3^9 frequency carrier.
--
-- Mathematical parent: DASHI.Core.CoarseFineRelativeFibreExact.
-- Specific jFine consumer: DASHI.Biology.JCoarseFineConsumerReductionBridgeExact.
-- Hardware architecture statements: SAXON Q, subject to source evidence.
-- This finite adapter: Johl Brown with OpenAI assistance, 2026-10-26.

open import DASHI.Core.Prelude
import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction

-- The existing core/fine geometry is a caller-supplied witness.  We
-- deliberately do not re-declare PR #1262's 16×8 Address or LocalGate.
-- `FineState` could denote a sufficiently rich implementation trace;
-- coarse is the public/core-level observation, relativeFine retains
-- a reconstruction witness / residual control trace.

consumerSafeCoreSummary :
  ∀ {FineState Action Observation}
    {step : Action → FineState → FineState}
    {observe : FineState → Observation}
    (geometry : Fibre.CoarseFineReopening FineState) →
    Fibre.CoarseDynamicsClosure geometry step →
    Fibre.CoarseConsumerFactorisation geometry observe →
    Reduction.ConsumerRelativeReduction FineState Action Observation
consumerSafeCoreSummary geometry dynamics consumer =
  Fibre.coarseProjectionAsExactReduction geometry dynamics consumer

consumerSafeCoreSummaryRetainsFine :
  ∀ {FineState Action Observation}
    {step : Action → FineState → FineState}
    {observe : FineState → Observation}
    (geometry : Fibre.CoarseFineReopening FineState) →
    (dynamics : Fibre.CoarseDynamicsClosure geometry step) →
    (consumer : Fibre.CoarseConsumerFactorisation geometry observe) →
    Reduction.ExactResidualReopening
      (consumerSafeCoreSummary geometry dynamics consumer)
consumerSafeCoreSummaryRetainsFine geometry dynamics consumer =
  Fibre.coarseProjectionRetainsRelativeFineResidual geometry dynamics consumer

-- A consumer that resolves a collision of coarse presentations forces
-- retention of the fine information: this is an already proved generic
-- theorem, specialized only by its consumer-facing name.
fineSensitiveNVConsumerObstructsCoarseOnly :
  ∀ {FineState Action Observation}
    {step : Action → FineState → FineState}
    {observe : FineState → Observation}
    (geometry : Fibre.CoarseFineReopening FineState) →
    Fibre.FineSensitiveConsumer geometry observe →
    Reduction.CandidateReductionFailure step observe (Fibre.coarse geometry)
fineSensitiveNVConsumerObstructsCoarseOnly geometry witness =
  Fibre.fineSensitivityRefutesCoarseOnlyReduction geometry witness

-- No assumptions about valid pulse calibration, physical inter-core
-- quantum link or laboratory measurements are discharged here.
