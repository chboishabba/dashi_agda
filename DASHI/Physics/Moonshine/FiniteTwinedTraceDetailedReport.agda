module DASHI.Physics.Moonshine.FiniteTwinedTraceDetailedReport where

open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Moonshine.FiniteGradedShellSeries as FGSS
open import DASHI.Physics.Moonshine.FiniteTwinedTraceComparison as FTC
open import DASHI.Physics.Moonshine.FiniteTwinerLibraryShift as TLS
open import DASHI.Physics.Moonshine.FiniteTwinerLibraryRootSystemB4 as TLB4
open import DASHI.Physics.Moonshine.FiniteGradedShellSeriesShift as FGSSS
open import DASHI.Physics.Moonshine.FiniteGradedShellSeriesRootSystemB4 as FGSSB4

record LabeledTwinedVerdict : Set where
  field
    shiftLabel : String
    b4Label : String
    comparison : FTC.FiniteTwinedTraceComparison
    verdict : FTC.FiniteTwinedTraceVerdict

mkVerdict :
  TLS.LabeledTwinedTrace →
  TLB4.LabeledTwinedTrace →
  LabeledTwinedVerdict
mkVerdict s b =
  let cmp =
        FTC.compareTwinedTrace
          (TLS.LabeledTwinedTrace.trace s)
          (TLB4.LabeledTwinedTrace.trace b)
  in
  record
    { shiftLabel = TLS.LabeledTwinedTrace.label s
    ; b4Label = TLB4.LabeledTwinedTrace.label b
    ; comparison = cmp
    ; verdict = FTC.classifyTwined cmp
    }

record FiniteTwinedTraceDetailedReport : Set where
  field
    shiftSeries : FGSS.FiniteGradedShellSeries
    b4Series : FGSS.FiniteGradedShellSeries
    identityVerdict : LabeledTwinedVerdict
    permutationVerdict : LabeledTwinedVerdict
    flipVerdict : LabeledTwinedVerdict
    extraVerdicts : List LabeledTwinedVerdict

finiteTwinedTraceDetailedReport : FiniteTwinedTraceDetailedReport
finiteTwinedTraceDetailedReport =
  record
    { shiftSeries = FGSSS.shiftFiniteGradedShellSeries
    ; b4Series = FGSSB4.b4FiniteGradedShellSeries
    ; identityVerdict = mkVerdict TLS.shiftTwinerIdentity TLB4.b4TwinerIdentity
    ; permutationVerdict = mkVerdict TLS.shiftTwinerPerm021 TLB4.b4TwinerPerm0132
    ; flipVerdict = mkVerdict TLS.shiftTwinerFlipT TLB4.b4TwinerFlip1
    ; extraVerdicts =
        mkVerdict TLS.shiftTwinerPerm120 TLB4.b4TwinerPerm1203 ∷
        mkVerdict TLS.shiftTwinerFlipSpace TLB4.b4TwinerFlipAll ∷
        []
    }
