module Ontology.Brain.BrainGaugeRobustnessReceipt where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import Ontology.Brain.BrainKernelClosureReceipt using
  (BrainKernelClosureReceipt; brainKernelClosureReceipt)

------------------------------------------------------------------------
-- Single-scale gauge-robustness receipt from dashiBRAIN Sprint 3.
-- The selected checksum set covers the baseline artifacts.  The alternate
-- gauge runs are recorded from docs/sprint-03.md as external numeric
-- diagnostics, not as independent checked artifacts in this module.

record BrainGaugeRunSummary : Set where
  constructor brainGaugeRunSummary
  field
    gaugeLabel : String
    deadzoneLabel : String
    defectTraceLabel : String
    finalDefect : Nat
    positiveComponentCount : Nat

sparseDCBaselineGauge : BrainGaugeRunSummary
sparseDCBaselineGauge =
  brainGaugeRunSummary
    "sparse_dc"
    "1e-9"
    "633,42,2,0"
    0
    8

sparseDCDz1e6Gauge : BrainGaugeRunSummary
sparseDCDz1e6Gauge =
  brainGaugeRunSummary
    "sparse_dc"
    "1e-6"
    "633,42,2,0"
    0
    8

sparseDCDz1e4Gauge : BrainGaugeRunSummary
sparseDCDz1e4Gauge =
  brainGaugeRunSummary
    "sparse_dc"
    "1e-4"
    "633,42,2,0"
    0
    8

rawDz1e9Gauge : BrainGaugeRunSummary
rawDz1e9Gauge =
  brainGaugeRunSummary
    "raw"
    "1e-9"
    "same final state and 8-component structure as sparse_dc"
    0
    8

record BrainGaugeRobustnessReceipt : Set₁ where
  field
    baselineClosureReceipt : BrainKernelClosureReceipt
    gaugeRuns : List BrainGaugeRunSummary
    singleScaleOnly : Bool
    promotesBrainLane : Bool
    robustnessBoundary : List String

brainGaugeRobustnessReceipt : BrainGaugeRobustnessReceipt
brainGaugeRobustnessReceipt =
  record
    { baselineClosureReceipt = brainKernelClosureReceipt
    ; gaugeRuns =
        sparseDCBaselineGauge
        ∷ sparseDCDz1e6Gauge
        ∷ sparseDCDz1e4Gauge
        ∷ rawDz1e9Gauge
        ∷ []
    ; singleScaleOnly = true
    ; promotesBrainLane = false
    ; robustnessBoundary =
        "Gauge robustness is limited to the Sprint 3 tested single-scale gauges"
        ∷ "Alternate gauge runs are doc-recorded external numeric diagnostics"
        ∷ "No new checksums beyond the selected artifact set are introduced here"
        ∷ "No learned weights, biological interpretation, or multiscale theorem is claimed"
        ∷ []
    }

baselineGaugeFinalDefectZero :
  BrainGaugeRunSummary.finalDefect sparseDCBaselineGauge ≡ zero
baselineGaugeFinalDefectZero = refl

gaugeReceiptIsSingleScaleOnly :
  BrainGaugeRobustnessReceipt.singleScaleOnly brainGaugeRobustnessReceipt
  ≡
  true
gaugeReceiptIsSingleScaleOnly = refl

gaugeReceiptDoesNotPromote :
  BrainGaugeRobustnessReceipt.promotesBrainLane brainGaugeRobustnessReceipt
  ≡
  false
gaugeReceiptDoesNotPromote = refl
