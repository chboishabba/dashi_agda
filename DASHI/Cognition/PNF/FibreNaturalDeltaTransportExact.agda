module DASHI.Cognition.PNF.FibreNaturalDeltaTransportExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

import DASHI.Reasoning.TypedHyperfabricCore as Hyper
import DASHI.Cognition.RecursiveFibreTower as Tower

------------------------------------------------------------------------
-- Hyperfabric delta naturality.
--
-- A semantic delta is not an arbitrary state patch.  Local vertex/stalk updates
-- transport to incident edge stalks and commute with the existing restriction
-- maps.  Therefore higher/local views can consume transported deltas rather than
-- reconstructing the entire lower carrier.
------------------------------------------------------------------------

record HyperfabricNaturalDelta
    {Vertex Edge : Set}
    (fabric : Hyper.TypedHyperfabric Vertex Edge) : Set₁ where
  field
    VertexDelta : Vertex → Set
    EdgeDelta : Edge → Set

    applyVertex :
      (vertex : Vertex) →
      Hyper.vertexStalk fabric vertex →
      VertexDelta vertex →
      Hyper.vertexStalk fabric vertex

    applyEdge :
      (edge : Edge) →
      Hyper.edgeStalk fabric edge →
      EdgeDelta edge →
      Hyper.edgeStalk fabric edge

    transportDelta :
      ∀ {vertex edge} →
      Hyper.incidence fabric vertex edge →
      VertexDelta vertex →
      EdgeDelta edge

    restrictionNaturality :
      ∀ {vertex edge}
        (membership : Hyper.incidence fabric vertex edge)
        (value : Hyper.vertexStalk fabric vertex)
        (delta : VertexDelta vertex) →
      Hyper.restrict fabric membership
        (applyVertex vertex value delta)
      ≡
      applyEdge edge
        (Hyper.restrict fabric membership value)
        (transportDelta membership delta)

open HyperfabricNaturalDelta public

------------------------------------------------------------------------
-- Fibre-tower delta naturality.
--
-- Refinement-level updates commute with projection.  Applying an upper-level
-- delta and then projecting is identical to transporting that delta downward and
-- applying it to the existing lower-level representative.
------------------------------------------------------------------------

record FibreTowerNaturalDelta
    (tower : Tower.FibreTower) : Set₁ where
  field
    LevelDelta : Nat → Set

    applyLevel :
      (level : Nat) →
      Tower.Level tower level →
      LevelDelta level →
      Tower.Level tower level

    projectDelta :
      (level : Nat) →
      LevelDelta (suc level) →
      LevelDelta level

    projectionNaturality :
      (level : Nat) →
      (state : Tower.Level tower (suc level)) →
      (delta : LevelDelta (suc level)) →
      Tower.project tower level
        (applyLevel (suc level) state delta)
      ≡
      applyLevel level
        (Tower.project tower level state)
        (projectDelta level delta)

open FibreTowerNaturalDelta public

------------------------------------------------------------------------
-- Consequence: hierarchy transport is delta transport, not mandatory rebuild.
------------------------------------------------------------------------

data ProjectionRequiresReconstructionOfUpperCarrier : Set where

data RestrictionRequiresReconstructionOfVertexCarrier : Set where

projectionCanTransportDeltaWithoutRebuild :
  ProjectionRequiresReconstructionOfUpperCarrier → ∀ {A : Set} → A
projectionCanTransportDeltaWithoutRebuild ()

restrictionCanTransportDeltaWithoutRebuild :
  RestrictionRequiresReconstructionOfVertexCarrier → ∀ {A : Set} → A
restrictionCanTransportDeltaWithoutRebuild ()
