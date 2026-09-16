module DASHI.Reasoning.TypedHyperfabricTransportReorganisationSeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Reasoning.TypedHyperfabricActionCrossingTransportExact as Crossing
import DASHI.Biology.RuinNarrativeReorganisationExact as Ruin
import DASHI.Biology.PsychogeographicFieldExact as Psychogeography

------------------------------------------------------------------------
-- WITHIN-FABRIC TRANSPORT != CROSS-FABRIC REORGANISATION
--
-- Existing owners already make these two semantic roles different:
--
--   crossing transport : GlobalSection H -> GlobalSection H
--   reorganisation     : TypedHyperfabric V E -> TypedHyperfabric V E
--                        with an explicit edge map/provenance law and declared
--                        incidence/transport/stalk-erasure boundaries.
--
-- This owner only records the separation and instantiates it on the existing
-- ruin/psychogeography witnesses.  It introduces no new transport or
-- reorganisation calculus.
------------------------------------------------------------------------

WithinFabricTransportSurface :
  {Vertex Edge Action : Set} →
  Hyperfabric.TypedHyperfabric Vertex Edge → Set₁
WithinFabricTransportSurface {Action = Action} fabric =
  Crossing.HyperfabricCrossingTransport {Action = Action} fabric

CrossFabricReorganisationSurface :
  {Vertex Edge : Set} →
  Hyperfabric.TypedHyperfabric Vertex Edge →
  Hyperfabric.TypedHyperfabric Vertex Edge → Set₁
CrossFabricReorganisationSurface = Hyperfabric.ProvenancePreservingReorganisation

ruinReorganisationChangesIncidenceWithoutStalkErasure :
  Hyperfabric.incidenceMayChange Ruin.ruinReorganisation ≡ true
  × Hyperfabric.stalkContentErased Ruin.ruinReorganisation ≡ false
ruinReorganisationChangesIncidenceWithoutStalkErasure = refl , refl

ruinReorganisationPreservesEdgeProvenance :
  (edge : Ruin.RuinEdge) →
  Hyperfabric.edgeProvenance Ruin.beforeRuinFabric edge
  ≡ Hyperfabric.edgeProvenance Ruin.afterRuinFabric
      (Hyperfabric.edgeMap Ruin.ruinReorganisation edge)
ruinReorganisationPreservesEdgeProvenance =
  Hyperfabric.provenancePreserved Ruin.ruinReorganisation

sameEndpointDoesNotDetermineTransportedPhase :
  Psychogeography.site
    (Psychogeography.finalState Psychogeography.memoryRoute)
  ≡
  Psychogeography.site
    (Psychogeography.finalState Psychogeography.reoccupationRoute)
  ×
  ¬
    (Psychogeography.phase
      (Psychogeography.finalState Psychogeography.memoryRoute)
    ≡
    Psychogeography.phase
      (Psychogeography.finalState Psychogeography.reoccupationRoute))
sameEndpointDoesNotDetermineTransportedPhase =
  Psychogeography.samePhysicalEndpoint ,
  Psychogeography.sameEndpointDoesNotForceSamePhase

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data WithinFabricTransportAutomaticallyConstructsCrossFabricReorganisation : Set where

data ProvenancePreservationForcesIncidencePreservation : Set where

data SameEndpointDeterminesPathState : Set where

withinFabricTransportDoesNotAutomaticallyConstructCrossFabricReorganisation :
  WithinFabricTransportAutomaticallyConstructsCrossFabricReorganisation → ⊥
withinFabricTransportDoesNotAutomaticallyConstructCrossFabricReorganisation ()

provenancePreservationDoesNotForceIncidencePreservation :
  ProvenancePreservationForcesIncidencePreservation → ⊥
provenancePreservationDoesNotForceIncidencePreservation ()

sameEndpointDoesNotDeterminePathState :
  SameEndpointDeterminesPathState → ⊥
sameEndpointDoesNotDeterminePathState ()

record TransportReorganisationBoundary : Set where
  constructor transport-reorganisation-boundary
  field
    crossingTransportStaysWithinOneFabric : Bool
    reorganisationMayChangeIncidence : Bool
    reorganisationMayChangeTransport : Bool
    reorganisationRequiresProvenanceLaw : Bool
    provenancePreservationImpliesStalkErasure : Bool
    provenancePreservationImpliesStalkErasureIsFalse :
      provenancePreservationImpliesStalkErasure ≡ false
    withinFabricTransportEqualsTopologyChange : Bool
    withinFabricTransportEqualsTopologyChangeIsFalse :
      withinFabricTransportEqualsTopologyChange ≡ false
    sameEndpointDeterminesTransportHistory : Bool
    sameEndpointDeterminesTransportHistoryIsFalse :
      sameEndpointDeterminesTransportHistory ≡ false
    boundaryNote : String

open TransportReorganisationBoundary public

canonicalTransportReorganisationBoundary : TransportReorganisationBoundary
canonicalTransportReorganisationBoundary =
  transport-reorganisation-boundary
    true
    true
    true
    true
    false refl
    false refl
    false refl
    "Section transport evolves a compatible state inside one fixed TypedHyperfabric. Provenance-preserving reorganisation is a separate cross-fabric operation that may alter incidence/transport without erasing stalk content. Psychogeographic routes additionally witness that a shared physical endpoint does not determine the path-dependent phase/history."
