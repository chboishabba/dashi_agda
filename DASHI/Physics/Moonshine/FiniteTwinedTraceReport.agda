module DASHI.Physics.Moonshine.FiniteTwinedTraceReport where

open import Agda.Primitive using (Set)

open import DASHI.Physics.Moonshine.FiniteGradedShellSeries as FGSS
open import DASHI.Physics.Moonshine.FiniteTwinedShellTrace as FTST
open import DASHI.Physics.Moonshine.FiniteTwinedTraceComparison as FTC
open import DASHI.Physics.Moonshine.FiniteTwinerLibraryShift as TLS
open import DASHI.Physics.Moonshine.FiniteTwinerLibraryRootSystemB4 as TLB4
open import DASHI.Physics.Moonshine.FiniteGradedShellSeriesShift as FGSSS
open import DASHI.Physics.Moonshine.FiniteGradedShellSeriesRootSystemB4 as FGSSB4

record FiniteTwinedTraceReport : Set where
  field
    shiftSeries : FGSS.FiniteGradedShellSeries
    b4Series : FGSS.FiniteGradedShellSeries
    identityComparison : FTC.FiniteTwinedTraceComparison
    identityVerdict : FTC.FiniteTwinedTraceVerdict
    selectedComparison : FTC.FiniteTwinedTraceComparison
    selectedVerdict : FTC.FiniteTwinedTraceVerdict

finiteTwinedTraceReport : FiniteTwinedTraceReport
finiteTwinedTraceReport =
  let
    identityCmp =
      FTC.compareTwinedTrace
        (TLS.LabeledTwinedTrace.trace TLS.shiftTwinerIdentity)
        (TLB4.LabeledTwinedTrace.trace TLB4.b4TwinerIdentity)
    selectedCmp =
      FTC.compareTwinedTrace
        (TLS.LabeledTwinedTrace.trace TLS.shiftTwinerPerm021)
        (TLB4.LabeledTwinedTrace.trace TLB4.b4TwinerPerm0132)
  in
  record
    { shiftSeries = FGSSS.shiftFiniteGradedShellSeries
    ; b4Series = FGSSB4.b4FiniteGradedShellSeries
    ; identityComparison = identityCmp
    ; identityVerdict = FTC.classifyTwined identityCmp
    ; selectedComparison = selectedCmp
    ; selectedVerdict = FTC.classifyTwined selectedCmp
    }
