module DASHI.Codec.IndexedAffineNativeGraphTransportExact where

-- H07 actual Base369 native HypervoxelAdjacent edge transport.
-- Uses original corner-appraisal fabric and selected pivot chart.
-- Does NOT claim naive native adjacency is invariant.
-- The source-specific pivot involution remains explicitly conditional.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Algebra.Trit as T
import DASHI.Codec.IndexedCubeAffineStableOverlapExact as Stable
import DASHI.Codec.IndexedCubePivot02RechartedExact as Pivot
import DASHI.Codec.IndexedAffineCornerAppraisal5832Exact as Native
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geo

Source : Set
Source = Stable.StableBlocks T.Trit

-- Actual original geometry, not an invented graph on equal-size sets.
NativeEdge : Source → Source → Set
NativeEdge x y =
  Geo.HyperformalAdjacent (Native.toFabric x) (Native.toFabric y)

-- On pivot chart coordinates a,b, inverse-map to the original source.
PivotEdge : Source → Source → Set
PivotEdge a b =
  NativeEdge (Pivot.pivotRaw a) (Pivot.pivotRaw b)

-- Correct forward edge transport (conditional on the actual F3 inverse).
sourceEdgeMovesToPivot :
  (laws : Pivot.SourcePivotInvolution) →
  (a b : Source) →
  NativeEdge a b →
  PivotEdge (Pivot.pivotRaw a) (Pivot.pivotRaw b)
sourceEdgeMovesToPivot laws a b edge
  rewrite Pivot.onRaw laws a
        | Pivot.onRaw laws b = edge

-- Correct backwards reconstruction needs no inverse law: it is the
-- very definition of the pulled-back selected edge relation.
pivotEdgeReopens :
  (a b : Source) →
  PivotEdge a b →
  NativeEdge (Pivot.pivotRaw a) (Pivot.pivotRaw b)
pivotEdgeReopens a b edge = edge

-- Exact operator/consumer comparisons should therefore use PivotEdge,
-- not naive Geo.HyperformalAdjacent at the pivot-coded native addresses.
-- Full integer Laplacian and Dirichlet energy acceptance is independent
-- locally executed Python/SymPy and not a claimed Agda theorem.
