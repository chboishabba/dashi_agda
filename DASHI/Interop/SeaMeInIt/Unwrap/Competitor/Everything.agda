module DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Everything where

open import Agda.Builtin.Bool using (Bool; true; false)

open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Core public
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Methods public
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Benchmark public
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Obligations public
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.GarmentGate public
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.ClaimBoundaries public
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.ExternalConformance public

------------------------------------------------------------------------
-- Umbrella surface
------------------------------------------------------------------------

record SeaMeInItUnwrapCompetitorSurface : Set₁ where
  field
    Method : Set
    RunReceipt : Set
    Benchmark : Set
    GarmentGate : Set
    methodFamilyTotal :
      Method →
      MethodFamily
    everyRunHasBoundary :
      RunReceipt →
      ClaimBoundary
    everyRunHasSeverity :
      RunReceipt →
      MethodSeverityReport
    benchmarkWinnerHasNoGlobalClaim :
      Benchmark →
      Set
    optionalUnavailableIsDiagnostic :
      Method →
      OptionalCompetitorBoundary →
      Set

open SeaMeInItUnwrapCompetitorSurface public
