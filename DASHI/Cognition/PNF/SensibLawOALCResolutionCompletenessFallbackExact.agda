module DASHI.Cognition.PNF.SensibLawOALCResolutionCompletenessFallbackExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawOALCLegislationParserInputContractExact as OALC

------------------------------------------------------------------------
-- OALC RESOLUTION COMPLETENESS / FALLBACK
--
-- Runtime parity for the governed OALC provider:
--
--   /filter exact row found
--      -> retain even when the viewer reports partial=true
--
--   /filter zero rows + complete index
--      -> explicit source residual for this exact demand
--
--   /filter zero rows + partial index
--      -> revision-pinned streaming fallback
--
--   streaming fallback unavailable / dependency missing / transport failure
--      -> SOURCE_RESIDUAL, never source absence and never negative legal evidence.
------------------------------------------------------------------------

data OALCFilterCompleteness : Set where
  completeIndex : OALCFilterCompleteness
  partialIndex : OALCFilterCompleteness

data OALCFilterRows : Set where
  zeroRows : OALCFilterRows
  oneOrMoreRows : OALCFilterRows

data OALCResolutionPath : Set where
  filterExact : OALCResolutionPath
  revisionPinnedStreaming : OALCResolutionPath

data OALCResolutionOutcome : Set where
  resolvedExactDocument : OALCResolutionOutcome
  explicitSourceResidual : OALCResolutionOutcome
  fallbackRequired : OALCResolutionOutcome

record OALCFilterObservation
    (demand : OALC.OALCLegislationSourceDemand) : Set where
  constructor oalc-filter-observation
  field
    rows : OALCFilterRows
    completeness : OALCFilterCompleteness
    exactDemandMatchRef : String
    observedDatasetRevisionRef : String
    observationAuthority : String

open OALCFilterObservation public

filterDisposition :
  ∀ {demand} →
  OALCFilterObservation demand →
  OALCResolutionOutcome
filterDisposition observation with rows observation | completeness observation
... | zeroRows | completeIndex = explicitSourceResidual
... | zeroRows | partialIndex = fallbackRequired
... | oneOrMoreRows | _ = resolvedExactDocument

record RevisionPinnedStreamingDemand
    (demand : OALC.OALCLegislationSourceDemand)
    (observation : OALCFilterObservation demand) : Set where
  constructor revision-pinned-streaming-demand
  field
    datasetRevisionRef : String
    exactCitationRef : String
    exactSourceRef : String
    exactJurisdictionRef : String
    exactDocumentTypeRef : String
    streamingAuthority : String

open RevisionPinnedStreamingDemand public

record OALCResolvedDocumentWithPath
    {dataset : OALC.OALCDatasetSelection}
    {demand : OALC.OALCLegislationSourceDemand}
    (receipt : OALC.OALCResolvedDocumentReceipt dataset demand) : Set where
  constructor oalc-resolved-document-with-path
  field
    resolutionPath : OALCResolutionPath
    resolutionEvidenceRef : String

open OALCResolvedDocumentWithPath public

------------------------------------------------------------------------
-- Source residual is epistemic/acquisition state only.
------------------------------------------------------------------------

data PartialZeroMeansSourceAbsent : Set where
data MissingStreamingDependencyMeansSourceAbsent : Set where
data StreamingFailureMeansNegativeLegalEvidence : Set where
data FilterExactOnPartialIndexMustFallback : Set where
data CompleteZeroCreatesNegativeLegalEvidence : Set where
data SourceResidualClosesLegalFollowFrontier : Set where

partialZeroDoesNotMeanSourceAbsent : PartialZeroMeansSourceAbsent → ⊥
partialZeroDoesNotMeanSourceAbsent ()

missingStreamingDependencyDoesNotMeanSourceAbsent :
  MissingStreamingDependencyMeansSourceAbsent → ⊥
missingStreamingDependencyDoesNotMeanSourceAbsent ()

streamingFailureDoesNotCreateNegativeLegalEvidence :
  StreamingFailureMeansNegativeLegalEvidence → ⊥
streamingFailureDoesNotCreateNegativeLegalEvidence ()

exactFilterHitDoesNotNeedFallbackMerelyBecausePartial :
  FilterExactOnPartialIndexMustFallback → ⊥
exactFilterHitDoesNotNeedFallbackMerelyBecausePartial ()

completeZeroDoesNotCreateNegativeLegalEvidence :
  CompleteZeroCreatesNegativeLegalEvidence → ⊥
completeZeroDoesNotCreateNegativeLegalEvidence ()

sourceResidualDoesNotCloseLegalFollowFrontier :
  SourceResidualClosesLegalFollowFrontier → ⊥
sourceResidualDoesNotCloseLegalFollowFrontier ()

record OALCResolutionCompletenessBoundary : Set where
  constructor oalc-resolution-completeness-boundary
  field
    exactRowAcceptedEvenWhenPartial : Bool
    completeZeroCreatesExplicitSourceResidual : Bool
    partialZeroRequiresPinnedStreamingFallback : Bool
    fallbackUsesObservedImmutableRevision : Bool
    missingStreamingDependencyCreatesSourceResidual : Bool
    sourceResidualCreatesNegativeLegalEvidence : Bool
    sourceResidualClosesLegalFollow : Bool

canonicalOALCResolutionCompletenessBoundary :
  OALCResolutionCompletenessBoundary
canonicalOALCResolutionCompletenessBoundary =
  oalc-resolution-completeness-boundary
    true true true true true false false
