module DASHI.Analysis.RiemannUniversalEvenConeHistoricalPointerResolutionValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Analysis.RiemannUniversalEvenConeHistoricalPointerResolutionExact as Owner

boundary : Owner.HistoricalPointerResolutionBoundary
boundary = Owner.canonicalHistoricalPointerResolutionBoundary

pointerRecorded : Bool
pointerRecorded = Owner.contentAddressedArchivePointerRecorded boundary

branchResolvable : Bool
branchResolvable = Owner.historicalBranchCurrentlyResolvable boundary

archiveAcquired : Bool
archiveAcquired = Owner.archiveBytesAcquired boundary

sourceRecovered : Bool
sourceRecovered = Owner.exactHistoricalTaperSourceRecovered boundary
