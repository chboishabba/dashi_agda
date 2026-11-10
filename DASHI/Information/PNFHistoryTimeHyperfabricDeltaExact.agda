module DASHI.Information.PNFHistoryTimeHyperfabricDeltaExact where

-- Time-indexed hyperfabric update for a *single selected* typed fabric.
-- Reuses existing GlobalSection and HyperfabricNaturalDelta, rather
-- than rebuilding stalks or identifying a numeric covariance spectrum
-- with the semantic hyperfabric.
--
-- The proof transports local vertex and edge updates through every
-- incidence restriction, provided the update is incidence-consistent.
-- The consumer/version and source history are explicitly separate.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Reasoning.TypedHyperfabricCore as Hyper
import DASHI.Cognition.PNF.FibreNaturalDeltaTransportExact as Delta

record TimedHyperformalSections
  (Vertex Edge : Set)
  (fabric : Hyper.TypedHyperfabric Vertex Edge) : Set₂ where
  field
    History : Set
    Time : Set
    sectionAt :
      History → Time → Hyper.GlobalSection fabric
    sourceAt : History → Time → String
    consumerVersionAt : History → Time → Nat

open TimedHyperformalSections public

-- A selected delta is a local stalk operation, not a new source truth.
record CoherentTimedHyperfabricDelta
  {Vertex Edge : Set}
  {fabric : Hyper.TypedHyperfabric Vertex Edge}
  (D : Delta.HyperfabricNaturalDelta fabric)
  (old : Hyper.GlobalSection fabric) : Set₁ where
  field
    vertexChange :
      (v : Vertex) → Delta.VertexDelta D v
    edgeChange :
      (e : Edge) → Delta.EdgeDelta D e
    incidentDeltaAgreement :
      {v : Vertex} {e : Edge} →
      (membership : Hyper.incidence fabric v e) →
      Delta.transportDelta D membership (vertexChange v)
      ≡ edgeChange e

open CoherentTimedHyperfabricDelta public

applyCoherentDelta :
  {Vertex Edge : Set}
  {fabric : Hyper.TypedHyperfabric Vertex Edge} →
  (D : Delta.HyperfabricNaturalDelta fabric) →
  (old : Hyper.GlobalSection fabric) →
  CoherentTimedHyperfabricDelta D old →
  Hyper.GlobalSection fabric
applyCoherentDelta {fabric = fabric} D old change = record
  { vertexValue =
      λ v → Delta.applyVertex D v
        (Hyper.vertexValue old v) (vertexChange change v)
  ; edgeValue =
      λ e → Delta.applyEdge D e
        (Hyper.edgeValue old e) (edgeChange change e)
  ; compatible =
      λ {v} {e} membership →
        trans
          (Delta.restrictionNaturality D membership
            (Hyper.vertexValue old v)
            (vertexChange change v))
          (trans
            (cong (Delta.applyEdge D e (Hyper.restrict fabric membership
                     (Hyper.vertexValue old v)))
              (incidentDeltaAgreement change membership))
            (cong (λ value →
              Delta.applyEdge D e value (edgeChange change e))
              (Hyper.compatible old membership)))
  ; sectionReceipt = Hyper.sectionReceipt old
  }

-- The checked construction retains the selected source time, but it
-- does not assert that an observed next section equals the computed
-- update. That equality is a separately paid transition receipt.
record ObservedTemporalDeltaStep
  {Vertex Edge : Set}
  {fabric : Hyper.TypedHyperfabric Vertex Edge}
  (D : Delta.HyperfabricNaturalDelta fabric)
  (old new : Hyper.GlobalSection fabric) : Set₁ where
  field
    sourceDelta : CoherentTimedHyperfabricDelta D old
    observedUpdateIsDerived :
      applyCoherentDelta D old sourceDelta ≡ new

open ObservedTemporalDeltaStep public

observedDeltaPreservesGlobalIncidence :
  {Vertex Edge : Set}
  {fabric : Hyper.TypedHyperfabric Vertex Edge} →
  (D : Delta.HyperfabricNaturalDelta fabric) →
  (old new : Hyper.GlobalSection fabric) →
  (step : ObservedTemporalDeltaStep D old new) →
  {v : Vertex} {e : Edge} →
  (membership : Hyper.incidence fabric v e) →
  Hyper.restrict fabric membership (Hyper.vertexValue new v)
  ≡ Hyper.edgeValue new e
observedDeltaPreservesGlobalIncidence D old new step membership =
  Hyper.compatible new membership
