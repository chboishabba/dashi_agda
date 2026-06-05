module DASHI.Interop.SeaMeInIt.Unwrap.Competitor.ExternalConformance where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe; just; nothing)

open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Core
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Methods
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Benchmark

------------------------------------------------------------------------
-- External tool / fast-path conformance receipts
------------------------------------------------------------------------

record ExternalImplementationReceipt : Set₁ where
  field
    methodKind : MethodKind
    toolName : String
    toolVersion : String
    settingsHash : String
    inputHash : String
    outputHash : Maybe String
    measuredRun : CompetitorRunReceipt
    measuredOnlyBoundary : Set
    noInternalProofAuthority : Set
    conformanceBoundary : List String

open ExternalImplementationReceipt public

record ExternalHarnessRunReceipt : Set₁ where
  field
    implementation : ExternalImplementationReceipt
    harnessName : String
    harnessVersion : String
    harnessSourceHash : String
    commandHash : String
    environmentHash : String
    artifactSchemaHash : String
    artifactHash : String
    metricsHash : String
    parsedRun : CompetitorRunReceipt
    parsedRunMatchesMeasuredRun :
      parsedRun
      ≡
      measuredRun implementation
    measuredOnlyBoundary : Set
    noHarnessProofAuthority : Set

open ExternalHarnessRunReceipt public

record SWARStyleConformance : Set₁ where
  field
    referenceRun : CompetitorRunReceipt
    optimizedRun : CompetitorRunReceipt
    packUnpackSection : Set
    unpackPackRetraction : Set
    packedOperationSound : Set
    severityPreserved : Set
    noClaimWithoutConformance : Set

open SWARStyleConformance public
