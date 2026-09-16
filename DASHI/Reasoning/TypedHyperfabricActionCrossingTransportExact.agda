module DASHI.Reasoning.TypedHyperfabricActionCrossingTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Core.ActionCrossingTraceCalculusExact as Trace
import DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact as Braid
import DASHI.Reasoning.TypedHyperfabricConsumerReductionBridgeExact as SectionReduction

------------------------------------------------------------------------
-- TYPED HYPERFABRIC ACTION-CROSSING TRANSPORT
--
-- ActionCrossingTraceCalculusExact already owns the ordered crossing grammar:
-- persistent strands, explicit pairwise crossing events, ordered traces, and
-- associative trace concatenation.  This bridge supplies the missing semantic
-- action on compatible TypedHyperfabric GlobalSections.
--
-- A domain supplies one section update per crossing event.  Because the output
-- type is again GlobalSection fabric, compatibility remains a typed obligation
-- at every step.  No reversibility, braid-group law, isotopy, or fusion rule is
-- inferred from the existence of this transport.
------------------------------------------------------------------------

record HyperfabricCrossingTransport
    {Vertex Edge Action : Set}
    (fabric : Hyperfabric.TypedHyperfabric Vertex Edge) : Set₁ where
  constructor hyperfabric-crossing-transport
  field
    crossingStep :
      Trace.CrossingEvent Edge Action →
      Hyperfabric.GlobalSection fabric →
      Hyperfabric.GlobalSection fabric
    crossingReceipt : Trace.CrossingEvent Edge Action → String
    transportReceipt : String

open HyperfabricCrossingTransport public

transportTrace :
  ∀ {Vertex Edge Action}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} →
  HyperfabricCrossingTransport {Action = Action} fabric →
  Trace.ActionTrace Edge Action →
  Hyperfabric.GlobalSection fabric →
  Hyperfabric.GlobalSection fabric
transportTrace transport [] section = section
transportTrace transport (event ∷ events) section =
  transportTrace transport events (crossingStep transport event section)

transportTraceAppend :
  ∀ {Vertex Edge Action}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} →
  (transport : HyperfabricCrossingTransport {Action = Action} fabric) →
  (left right : Trace.ActionTrace Edge Action) →
  (section : Hyperfabric.GlobalSection fabric) →
  transportTrace transport (left Trace.++trace right) section
  ≡ transportTrace transport right (transportTrace transport left section)
transportTraceAppend transport [] right section = refl
transportTraceAppend transport (event ∷ events) right section =
  transportTraceAppend transport events right
    (crossingStep transport event section)

traceOrderRemainsProvenance :
  Trace.crossingOrderIsFirstClass Trace.canonicalActionCrossingTraceBoundary ≡ true
traceOrderRemainsProvenance = refl

crossingCoordinationDoesNotFuseStrands :
  Braid.coordinationWithoutFusion Braid.canonicalBraidedEvidenceBoundary ≡ true
crossingCoordinationDoesNotFuseStrands = refl

------------------------------------------------------------------------
-- Finite specimen: one explicit crossing acts as identity on the existing
-- compatible section fixture.  The point is the transport typing, not the
-- identity action itself.
------------------------------------------------------------------------

finiteCrossing : Trace.CrossingEvent SectionReduction.SpecEdge ⊤
finiteCrossing =
  Trace.crossing-event
    SectionReduction.relation
    SectionReduction.relation
    tt

finiteTransport : HyperfabricCrossingTransport {Action = ⊤} SectionReduction.specFabric
finiteTransport = hyperfabric-crossing-transport
  (λ _ section → section)
  (λ _ → "finite crossing keeps the compatible section unchanged")
  "identity transport specimen over one explicit ordered crossing"

finiteTrace : Trace.ActionTrace SectionReduction.SpecEdge ⊤
finiteTrace = Trace.singleCrossing finiteCrossing

finiteTraceTransportPreservesCompatibleSection :
  transportTrace finiteTransport finiteTrace SectionReduction.leftSection
  ≡ SectionReduction.leftSection
finiteTraceTransportPreservesCompatibleSection = refl

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data CrossingTransportImpliesUniversalReversibility : Set where
data CrossingTransportConstructsBraidGroup : Set where
data CrossingTransportFusesEdgeStrands : Set where

crossingTransportDoesNotImplyUniversalReversibility :
  CrossingTransportImpliesUniversalReversibility → ⊥
crossingTransportDoesNotImplyUniversalReversibility ()

crossingTransportDoesNotConstructBraidGroup :
  CrossingTransportConstructsBraidGroup → ⊥
crossingTransportDoesNotConstructBraidGroup ()

crossingTransportDoesNotFuseEdgeStrands :
  CrossingTransportFusesEdgeStrands → ⊥
crossingTransportDoesNotFuseEdgeStrands ()

record TypedHyperfabricActionCrossingBoundary : Set where
  constructor typed-hyperfabric-action-crossing-boundary
  field
    orderedCrossingTraceReused : Bool
    crossingStepMapsCompatibleSectionToCompatibleSection : Bool
    traceConcatenationComposesSectionTransport : Bool
    crossingOrderRetainedAsProvenance : Bool
    crossingTransportAutomaticallyReversible : Bool
    crossingTransportAutomaticallyReversibleIsFalse :
      crossingTransportAutomaticallyReversible ≡ false
    actionTraceAutomaticallyBraidGroupElement : Bool
    actionTraceAutomaticallyBraidGroupElementIsFalse :
      actionTraceAutomaticallyBraidGroupElement ≡ false
    crossingTransportFusesPersistentEdgeStrands : Bool
    crossingTransportFusesPersistentEdgeStrandsIsFalse :
      crossingTransportFusesPersistentEdgeStrands ≡ false
    endpointDeterminesFullTraceProvenance : Bool
    endpointDeterminesFullTraceProvenanceIsFalse :
      endpointDeterminesFullTraceProvenance ≡ false
    transportCreatesParallelHyperfabricKernel : Bool
    transportCreatesParallelHyperfabricKernelIsFalse :
      transportCreatesParallelHyperfabricKernel ≡ false
    boundaryNote : String

open TypedHyperfabricActionCrossingBoundary public

canonicalTypedHyperfabricActionCrossingBoundary :
  TypedHyperfabricActionCrossingBoundary
canonicalTypedHyperfabricActionCrossingBoundary =
  typed-hyperfabric-action-crossing-boundary
    true
    true
    true
    true
    false refl
    false refl
    false refl
    false refl
    false refl
    "Ordered crossing traces transport compatible GlobalSections through a domain-supplied crossingStep. Trace order remains provenance; no universal inverse, braid-group structure, edge fusion, or endpoint-complete history is promoted."

transportDoesNotImplyCrossingReversibility :
  crossingTransportAutomaticallyReversible
    canonicalTypedHyperfabricActionCrossingBoundary ≡ false
transportDoesNotImplyCrossingReversibility = refl

transportDoesNotPromoteTraceToBraidGroup :
  actionTraceAutomaticallyBraidGroupElement
    canonicalTypedHyperfabricActionCrossingBoundary ≡ false
transportDoesNotPromoteTraceToBraidGroup = refl
