module DASHI.Physics.Moonshine.MoonshinePrototypeComparisonBundle where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)

open import DASHI.Physics.Moonshine.FiniteTwinedTraceDetailedReport as FTDR
open import DASHI.Physics.Moonshine.TwinedComparisonSummary as TCS
open import DASHI.Physics.Moonshine.WaveGradedShellPrototypeSummary as WGSP

record MoonshinePrototypeComparisonBundle : Set where
  field
    detailedReport : FTDR.FiniteTwinedTraceDetailedReport
    comparisonSummary : TCS.TwinedComparisonSummary
    waveSummary : WGSP.WaveGradedShellPrototypeSummary
    comparedTwinerCount : Nat

canonicalMoonshinePrototypeComparisonBundle :
  MoonshinePrototypeComparisonBundle
canonicalMoonshinePrototypeComparisonBundle =
  record
    { detailedReport = FTDR.finiteTwinedTraceDetailedReport
    ; comparisonSummary = TCS.canonicalTwinedComparisonSummary
    ; waveSummary = WGSP.shiftWaveGradedShellPrototypeSummary
    ; comparedTwinerCount =
        length
          (FTDR.FiniteTwinedTraceDetailedReport.extraVerdicts
            FTDR.finiteTwinedTraceDetailedReport)
    }
