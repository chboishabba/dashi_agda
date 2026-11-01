module DASHI.Reasoning.TypedHyperfabricLocalRefinementBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Cognition.PNF.FibreNaturalDeltaTransportExact as Natural
import DASHI.Topology.TetrationalGateField as Gate

------------------------------------------------------------------------
-- TYPED HYPERFABRIC LOCAL REFINEMENT ROLE ADAPTER
--
-- The repository already has the stronger generic owner:
--   DASHI.Cognition.PNF.FibreNaturalDeltaTransportExact.HyperfabricNaturalDelta
--
-- It supplies vertex/edge delta types, local application, incidence transport,
-- and the exact restriction-naturality square.  This file therefore does NOT
-- define another refinement carrier.  It only exposes that owner at the local-
-- fibre role boundary and pins chart refinement apart from fibre-dimension and
-- tower transitions.
------------------------------------------------------------------------

HyperfabricNaturalDeltaSurface :
  {Vertex Edge : Set} →
  Hyperfabric.TypedHyperfabric Vertex Edge → Set₁
HyperfabricNaturalDeltaSurface = Natural.HyperfabricNaturalDelta

transportDeltaSurface :
  ∀ {Vertex Edge}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} →
  (deltaSystem : HyperfabricNaturalDeltaSurface fabric) →
  ∀ {vertex edge} →
  Hyperfabric.incidence fabric vertex edge →
  Natural.VertexDelta deltaSystem vertex →
  Natural.EdgeDelta deltaSystem edge
transportDeltaSurface = Natural.transportDelta

restrictionNaturalitySurface :
  ∀ {Vertex Edge}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge} →
  (deltaSystem : HyperfabricNaturalDeltaSurface fabric) →
  ∀ {vertex edge}
    (membership : Hyperfabric.incidence fabric vertex edge)
    (value : Hyperfabric.vertexStalk fabric vertex)
    (delta : Natural.VertexDelta deltaSystem vertex) →
  Hyperfabric.restrict fabric membership
    (Natural.applyVertex deltaSystem vertex value delta)
  ≡
  Natural.applyEdge deltaSystem edge
    (Hyperfabric.restrict fabric membership value)
    (Natural.transportDelta deltaSystem membership delta)
restrictionNaturalitySurface = Natural.restrictionNaturality

localRefinementDoesNotOpenTower :
  Gate.refineWithinChart ≡ Gate.openTowerLevel → ⊥
localRefinementDoesNotOpenTower ()

localRefinementDoesNotIncreaseFibreDimension :
  Gate.refineWithinChart ≡ Gate.increaseFibreDimension → ⊥
localRefinementDoesNotIncreaseFibreDimension ()

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

record TypedHyperfabricLocalRefinementBoundary : Set where
  constructor typed-hyperfabric-local-refinement-boundary
  field
    typedHyperfabricCoreRemainsCanonicalKernel : Bool
    canonicalNaturalDeltaOwnerReused : Bool
    vertexDeltaTransportedToIncidentEdgeDelta : Bool
    restrictionNaturalityRequired : Bool
    refinementActsOnDeclaredVertexStalkValues : Bool
    refinementImpliesIncreaseFibreDimension : Bool
    refinementImpliesIncreaseFibreDimensionIsFalse :
      refinementImpliesIncreaseFibreDimension ≡ false
    refinementImpliesOpenTowerLevel : Bool
    refinementImpliesOpenTowerLevelIsFalse :
      refinementImpliesOpenTowerLevel ≡ false
    localRefinementBridgeDefinesParallelDeltaKernel : Bool
    localRefinementBridgeDefinesParallelDeltaKernelIsFalse :
      localRefinementBridgeDefinesParallelDeltaKernel ≡ false
    boundaryNote : String

open TypedHyperfabricLocalRefinementBoundary public

canonicalTypedHyperfabricLocalRefinementBoundary :
  TypedHyperfabricLocalRefinementBoundary
canonicalTypedHyperfabricLocalRefinementBoundary =
  typed-hyperfabric-local-refinement-boundary
    true
    true
    true
    true
    true
    false refl
    false refl
    false refl
    "Local hyperfabric refinement reuses FibreNaturalDeltaTransportExact: vertex deltas transport to incident edge deltas and commute with restriction. refineWithinChart remains distinct from fibre-dimension increase and tower opening; no second refinement kernel is introduced."
