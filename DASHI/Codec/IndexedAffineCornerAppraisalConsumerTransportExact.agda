module DASHI.Codec.IndexedAffineCornerAppraisalConsumerTransportExact where

-- H07 same-object native geometry consumer: pivot02 is a reversible
-- coordinate rechart, not a native grid graph automorphism.
-- The only uninhabited premise is the existing F3 SourcePivotInvolution.
-- Reuse original corner/appraisal codec and conditional pivot02 witness.
-- Agda kernel not run; independent finite SymPy acceptance recorded.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Codec.IndexedCubeAffineStableOverlapExact as Stable
import DASHI.Codec.IndexedCubePivot02RechartedExact as Pivot
import DASHI.Codec.IndexedAffineCornerAppraisal5832Exact as Native
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geo
import DASHI.Algebra.Trit as Trit

Source : Set
Source = Stable.StableBlocks Trit.Trit

-- This is the EXACT original native corner × appraisal object, not
-- a new nine-trit representation based only on equal cardinality.
nativeObservation : Source → Native.NativeCornerAppraisal
nativeObservation = Native.toNativeCornerAppraisal

-- Correct coordinate transport of ANY native observer: decode first.
-- A caller need not assert that raw pivot preserves corner, appraisal,
-- physical adjacency, or a consumer not known to be invariant.
transportedObserver :
  ∀ {Outcome : Set} →
  (Source → Outcome) → Source → Outcome
transportedObserver consume coordinates =
  consume (Pivot.pivotRaw coordinates)

transportedNativeObservation : Source → Native.NativeCornerAppraisal
transportedNativeObservation = transportedObserver nativeObservation

-- Exact naturality is conditional on the *actual* selected involution.
transportedObserverRecovers :
  (laws : Pivot.SourcePivotInvolution) →
  ∀ {Outcome : Set} (consume : Source → Outcome) (x : Source) →
  transportedObserver consume (Pivot.pivotRaw x) ≡ consume x
transportedObserverRecovers laws consume x
  rewrite Pivot.onRaw laws x = refl

transportedNativeReopens :
  (laws : Pivot.SourcePivotInvolution) (x : Source) →
  transportedNativeObservation (Pivot.pivotRaw x)
    ≡ nativeObservation x
transportedNativeReopens laws =
  transportedObserverRecovers laws nativeObservation

-- A native consumer can instead be applied after exact native reopening
-- through the original Corner3 × AppraisalFibrePoint codec.
nativeConsumer :
  ∀ {Outcome : Set} →
  (Native.NativeCornerAppraisal → Outcome) → Source → Outcome
nativeConsumer consume x = consume (nativeObservation x)

transportedNativeConsumer :
  ∀ {Outcome : Set} →
  (Native.NativeCornerAppraisal → Outcome) → Source → Outcome
transportedNativeConsumer consume x =
  consume (transportedNativeObservation x)

nativeConsumerNaturality :
  (laws : Pivot.SourcePivotInvolution) →
  ∀ {Outcome : Set}
  (consume : Native.NativeCornerAppraisal → Outcome)
  (x : Source) →
  transportedNativeConsumer consume (Pivot.pivotRaw x)
    ≡ nativeConsumer consume x
nativeConsumerNaturality laws consume x
  rewrite transportedNativeReopens laws x = refl

-- The original full Base369 fabric observation also transports,
-- conditional on the same already-declared F3 involution.
nativeFabricNaturality :
  (laws : Pivot.SourcePivotInvolution) (x : Source) →
  Stable.toAffine (Pivot.pivotRaw (Pivot.pivotRaw x))
    ≡ Stable.toAffine x
nativeFabricNaturality laws x
  rewrite Pivot.onRaw laws x = refl

-- No equivalence of Geo.HyperformalAdjacent is inferred here.
-- The native grid adjacency is a separate edge relation.
