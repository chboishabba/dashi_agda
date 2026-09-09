module DASHI.Moonshine.JInvariant369ConsumerIndexedCodecRoutingExact where

------------------------------------------------------------------------
-- CONSUMER-INDEXED CODEC ROUTING FOR THE FORMULAIC J FIBRE
--
-- Reuse the repository's distinction between representation cost and semantic
-- execution.  A consumer may discard a residual only after proving it factors
-- through the corresponding finite observer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Moonshine.JInvariant369CodecReconciliationFrontierExact as Compact
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369FibreObserverRepairExact as Repair
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein

------------------------------------------------------------------------
-- 1. Consumers that factor through the 9-sheet may use the total compact
--    centre/3-bit code and discard the 27-frame residual.
------------------------------------------------------------------------

nineConsumerRoundTrip :
  ∀ {A : Set} →
  (consume : Triadic.NineSheet → A) →
  (sheet : Triadic.NineSheet) →
  consume (Compact.decodeCompactNine (Compact.encodeCompactNine sheet))
  ≡ consume sheet
nineConsumerRoundTrip consume sheet =
  cong consume (Compact.decodeEncodeCompactNine sheet)

------------------------------------------------------------------------
-- 2. Consumers of the 27/pants state require the explicit frame trit but may
--    still discard the analytic J payload after the 27-state is acquired.
------------------------------------------------------------------------

twentySevenConsumerRoundTrip :
  ∀ {A : Set} →
  (consume : Fabric.Ternary27Point → A) →
  (point : Fabric.Ternary27Point) →
  consume (Compact.decodeCompact27 (Compact.encodeCompact27 point))
  ≡ consume point
twentySevenConsumerRoundTrip consume point =
  cong consume (Compact.decodeEncodeCompact27 point)

------------------------------------------------------------------------
-- 3. Same-point renderer views.  These are routing helpers, not an assertion
--    that analytic value/phase/tone/RGB can be reconstructed from finite code.
------------------------------------------------------------------------

nineAt :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : Repair.SamePointFibreObservers R) →
  Klein.Point (Render.klein R) → Triadic.NineSheet
nineAt R F = Repair.observer9At F

twentySevenAt :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : Repair.SamePointFibreObservers R) →
  Klein.Point (Render.klein R) → Fabric.Ternary27Point
twentySevenAt R F = Repair.observer27At F

------------------------------------------------------------------------
-- 4. Routing policy.
------------------------------------------------------------------------

data JCodecConsumerClass : Set where
  nineSheetOnly : JCodecConsumerClass
  twentySevenOrPants : JCodecConsumerClass
  analyticPhaseToneOrRGB : JCodecConsumerClass

data JCodecRetention : Set where
  retainCompactNineOnly : JCodecRetention
  retainCompactNinePlusFrame : JCodecRetention
  retainFullAnalyticFibre : JCodecRetention

routeConsumer : JCodecConsumerClass → JCodecRetention
routeConsumer nineSheetOnly = retainCompactNineOnly
routeConsumer twentySevenOrPants = retainCompactNinePlusFrame
routeConsumer analyticPhaseToneOrRGB = retainFullAnalyticFibre

record JInvariant369ConsumerIndexedCodecBoundary : Set where
  constructor j-invariant-369-consumer-indexed-codec-boundary
  field
    nineConsumersMayDiscardFrameAfterDescent : Bool
    pantsConsumersMustRetainFrame : Bool
    analyticConsumersMustRetainContinuousPayload : Bool
    compactNineRoundTripPaysNineConsumers : Bool
    compactTwentySevenRoundTripPaysPantsConsumers : Bool
    logicalCellCountEqualsPhysicalCost : Bool
    physicalCompressionOptimalityClaimed : Bool

canonicalJInvariant369ConsumerIndexedCodecBoundary :
  JInvariant369ConsumerIndexedCodecBoundary
canonicalJInvariant369ConsumerIndexedCodecBoundary =
  j-invariant-369-consumer-indexed-codec-boundary
    true true true true true false false
