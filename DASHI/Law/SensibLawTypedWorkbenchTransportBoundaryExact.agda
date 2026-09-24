module DASHI.Law.SensibLawTypedWorkbenchTransportBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Interop.PortableInteractiveGpuProjectionExact as PortableGpu
import DASHI.Law.SensibLawUnifiedWorkbenchDioxusWgpuBridgeExact as WorkbenchGpu

------------------------------------------------------------------------
-- M11 PRODUCTION TRANSPORT OWNERSHIP
--
-- Canonical production path:
--
--   PostgreSQL typed rows
--      -> typed Rust PersistedWorkbenchProjection
--      -> typed Rust ComparativeWorkbenchProjection
--      -> Dioxus / wgpu projection
--
-- JSON/serialization may replay/export the typed projection, but it is not the
-- production semantic ABI and cannot become graph/provenance authority.
------------------------------------------------------------------------

data WorkbenchCarrier : Set where
  postgresTypedRows : WorkbenchCarrier
  typedRustPersistedProjection : WorkbenchCarrier
  typedRustComparativeProjection : WorkbenchCarrier
  jsonReplayBundle : WorkbenchCarrier
  dioxusProjection : WorkbenchCarrier
  wgpuProjection : WorkbenchCarrier

data ProductionStep : WorkbenchCarrier → WorkbenchCarrier → Set where
  postgresToTyped :
    ProductionStep postgresTypedRows typedRustPersistedProjection
  typedToComparative :
    ProductionStep typedRustPersistedProjection typedRustComparativeProjection
  comparativeToDioxus :
    ProductionStep typedRustComparativeProjection dioxusProjection
  dioxusToWgpu :
    ProductionStep dioxusProjection wgpuProjection

data ReplayStep : WorkbenchCarrier → WorkbenchCarrier → Set where
  typedToJsonReplay :
    ReplayStep typedRustPersistedProjection jsonReplayBundle
  comparativeToJsonReplay :
    ReplayStep typedRustComparativeProjection jsonReplayBundle

productionSpineExists :
  ProductionStep postgresTypedRows typedRustPersistedProjection
  × ProductionStep typedRustPersistedProjection typedRustComparativeProjection
  × ProductionStep typedRustComparativeProjection dioxusProjection
  × ProductionStep dioxusProjection wgpuProjection
productionSpineExists =
  postgresToTyped ,
  typedToComparative ,
  comparativeToDioxus ,
  dioxusToWgpu

jsonReplayIsOptionalSidePath :
  ReplayStep typedRustPersistedProjection jsonReplayBundle
jsonReplayIsOptionalSidePath = typedToJsonReplay

interactiveBoundary :
  PortableGpu.PortableInteractiveGpuProjectionBoundary
interactiveBoundary =
  PortableGpu.canonicalPortableInteractiveGpuProjectionBoundary

jsonCommandTransportAlreadyForbidden :
  PortableGpu.PortableInteractiveGpuProjectionBoundary.jsonSemanticCommandTransport
    interactiveBoundary
    ≡ false
jsonCommandTransportAlreadyForbidden = refl

workbenchBoundary :
  WorkbenchGpu.UnifiedWorkbenchDioxusWgpuBoundary
workbenchBoundary =
  WorkbenchGpu.canonicalUnifiedWorkbenchDioxusWgpuBoundary

dioxusStillProjectionNotAuthority :
  WorkbenchGpu.UnifiedWorkbenchDioxusWgpuBoundary.dioxusIsProjectionNotAuthority
    workbenchBoundary
    ≡ true
dioxusStillProjectionNotAuthority = refl

wgpuStillProjectionNotAuthority :
  WorkbenchGpu.UnifiedWorkbenchDioxusWgpuBoundary.wgpuIsProjectionNotAuthority
    workbenchBoundary
    ≡ true
wgpuStillProjectionNotAuthority = refl

data JsonReplayIsCanonicalProductionAbi : Set where
data JsonReplayCreatesGraphAuthority : Set where
data JsonReplayCreatesProvenanceAuthority : Set where
data DioxusReconstructsMissingSemanticGraph : Set where
data WgpuReconstructsMissingSemanticGraph : Set where
data SerializationCreatesClaimTruth : Set where

jsonReplayIsNotCanonicalProductionAbi :
  JsonReplayIsCanonicalProductionAbi → ⊥
jsonReplayIsNotCanonicalProductionAbi ()

jsonReplayDoesNotCreateGraphAuthority :
  JsonReplayCreatesGraphAuthority → ⊥
jsonReplayDoesNotCreateGraphAuthority ()

jsonReplayDoesNotCreateProvenanceAuthority :
  JsonReplayCreatesProvenanceAuthority → ⊥
jsonReplayDoesNotCreateProvenanceAuthority ()

dioxusDoesNotReconstructMissingSemanticGraph :
  DioxusReconstructsMissingSemanticGraph → ⊥
dioxusDoesNotReconstructMissingSemanticGraph ()

wgpuDoesNotReconstructMissingSemanticGraph :
  WgpuReconstructsMissingSemanticGraph → ⊥
wgpuDoesNotReconstructMissingSemanticGraph ()

serializationDoesNotCreateClaimTruth :
  SerializationCreatesClaimTruth → ⊥
serializationDoesNotCreateClaimTruth ()

record TypedWorkbenchTransportBoundary : Set where
  constructor typedWorkbenchTransportBoundary
  field
    postgresRowsAreProductionAuthorityInput : Bool
    postgresRowsAreProductionAuthorityInputIsTrue :
      postgresRowsAreProductionAuthorityInput ≡ true

    typedRustIsProductionWorkbenchCarrier : Bool
    typedRustIsProductionWorkbenchCarrierIsTrue :
      typedRustIsProductionWorkbenchCarrier ≡ true

    jsonIsReplayExportOnly : Bool
    jsonIsReplayExportOnlyIsTrue :
      jsonIsReplayExportOnly ≡ true

    jsonIsRequiredForNormalComparison : Bool
    jsonIsRequiredForNormalComparisonIsFalse :
      jsonIsRequiredForNormalComparison ≡ false

    dioxusOwnsSemanticComparison : Bool
    dioxusOwnsSemanticComparisonIsFalse :
      dioxusOwnsSemanticComparison ≡ false

    wgpuOwnsSemanticComparison : Bool
    wgpuOwnsSemanticComparisonIsFalse :
      wgpuOwnsSemanticComparison ≡ false

    transportCreatesSemanticAuthority : Bool
    transportCreatesSemanticAuthorityIsFalse :
      transportCreatesSemanticAuthority ≡ false

    transportCreatesClaimTruth : Bool
    transportCreatesClaimTruthIsFalse :
      transportCreatesClaimTruth ≡ false

open TypedWorkbenchTransportBoundary public

canonicalTypedWorkbenchTransportBoundary :
  TypedWorkbenchTransportBoundary
canonicalTypedWorkbenchTransportBoundary =
  typedWorkbenchTransportBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
