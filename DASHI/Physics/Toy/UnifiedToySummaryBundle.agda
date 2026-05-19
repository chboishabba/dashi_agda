module DASHI.Physics.Toy.UnifiedToySummaryBundle where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.CLOCKPhaseSummaryBundle as CLOCK
open import DASHI.Physics.Toy.RGSummaryBundle as RG
open import DASHI.Physics.Toy.GaugeSummaryBundle as Gauge
open import DASHI.Physics.Toy.RGUniversality as RGBase
open import DASHI.Physics.Toy.GaugeShell as GaugeBase

record UnifiedToySummaryBundle : Set₁ where
  field
    clock : CLOCK.ClockClosureConsumer

unifiedToySummaryBundle : UnifiedToySummaryBundle
unifiedToySummaryBundle =
  record
    { clock = CLOCK.clockClosureConsumer
    }

record UnifiedToyIterateBundle (n : Nat) : Set₁ where
  field
    rg-renormalization : RG.RGRenormalizationSummary
    rg-flow            : RG.RGFlowSummary
    rg-fused           : RG.RGFusedSummary
    rg-phase2-hierarchy : RG.RGPhase2HierarchySummary
    rg-prediction      : RG.RGPredictionSummary n
    rg-scheduled-prediction : RG.RGScheduledPredictionSummary n
    rg-benchmark       : RG.RGBenchmarkSummary n
    rg-rich-benchmark  : RG.RGRichBenchmarkSummary n
    rg-scheduled-benchmark : RG.RGScheduledBenchmarkSummary n
    rg-mixed-scheduled-benchmark : (k : Nat) → RG.RGMixedScheduledBenchmarkSummary n k
    rg-mixed-trace-benchmark : (k : Nat) → RG.RGMixedTraceBenchmarkSummary n k
    rg-mixed-phase2-trace-benchmark : (k : Nat) → RG.RGMixedPhase2TraceBenchmarkSummary n k
    rg-benchmark-compare : RG.RGBenchmarkComparisonBundle n
    rg-asymptotic :
      (x : RGBase.RGState n) →
      RG.RGAsymptoticBundle n x
    rg-recovered-tail :
      (k : Nat) →
      (x : RGBase.RGState n) →
      RG.RGRecoveredTailBundle n k x
    gauge-asymptotic :
      (x : GaugeBase.GaugeState n) →
      Gauge.GaugeAsymptoticBundle n x
    gauge-recovered-tail :
      (k : Nat) →
      (x : GaugeBase.GaugeState n) →
      Gauge.GaugeRecoveredTailBundle n k x

unifiedToyIterateBundle : (n : Nat) → UnifiedToyIterateBundle n
unifiedToyIterateBundle n =
  record
    { rg-renormalization = RG.rgRenormalizationSummary
    ; rg-flow = RG.rgFlowSummary
    ; rg-fused = RG.rgFusedSummary
    ; rg-phase2-hierarchy = RG.rgPhase2HierarchySummary
    ; rg-prediction = RG.rgPredictionSummary n
    ; rg-scheduled-prediction = RG.rgScheduledPredictionSummary n
    ; rg-benchmark = RG.rgBenchmarkSummary n
    ; rg-rich-benchmark = RG.rgRichBenchmarkSummary n
    ; rg-scheduled-benchmark = RG.rgScheduledBenchmarkSummary n
    ; rg-mixed-scheduled-benchmark = RG.rgMixedScheduledBenchmarkSummary n
    ; rg-mixed-trace-benchmark = RG.rgMixedTraceBenchmarkSummary n
    ; rg-mixed-phase2-trace-benchmark = RG.rgMixedPhase2TraceBenchmarkSummary n
    ; rg-benchmark-compare = RG.rgBenchmarkComparisonBundle n
    ; rg-asymptotic = RG.rgAsymptoticBundle n
    ; rg-recovered-tail = RG.rgRecoveredTailBundle n
    ; gauge-asymptotic = Gauge.gaugeAsymptoticBundle n
    ; gauge-recovered-tail = Gauge.gaugeRecoveredTailBundle n
    }
