module DASHI.Physics.Moonshine.TwinedComparisonSummary where

open import Agda.Primitive using (Set)

open import DASHI.Physics.Moonshine.FiniteTwinedTraceDetailedReport as FTDR
open import DASHI.Physics.Moonshine.WaveGradedShellPrototypeSummary as WGSP

record TwinedComparisonSummary : Set where
  field
    detailedReport : FTDR.FiniteTwinedTraceDetailedReport
    waveSummary : WGSP.WaveGradedShellPrototypeSummary

canonicalTwinedComparisonSummary : TwinedComparisonSummary
canonicalTwinedComparisonSummary =
  record
    { detailedReport = FTDR.finiteTwinedTraceDetailedReport
    ; waveSummary = WGSP.shiftWaveGradedShellPrototypeSummary
    }
