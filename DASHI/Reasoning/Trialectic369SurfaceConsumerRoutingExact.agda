module DASHI.Reasoning.Trialectic369SurfaceConsumerRoutingExact where

------------------------------------------------------------------------
-- GENERIC T^3 SURFACE -> TRIALECTIC GEOMETRIC CONSUMER ROUTING
--
-- DASHI CONTRIBUTION
--
-- Any upstream state that exposes a Ternary27Point may feed the declared-row
-- trialectic geometry.  The downstream matrix, hyperfabric and Rubik views
-- consume only that T^3 surface.  Therefore they factor through the surface
-- observer and do not require any upstream residual merely to construct these
-- geometric views.
--
-- This theorem is generic in the upstream State.  It does not identify any
-- upstream semantics with relational participant A/B/C, and it says nothing
-- about upstream consumers (such as arithmetic magnitudes) that do not descend
-- through the T^3 surface.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as Bridge
import DASHI.Reasoning.Trialectic369RubikRefinementExact as Rubik
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Reasoning.Trialectic369DeclaredRowConsumerExact as Declared

------------------------------------------------------------------------
-- 1. Surface-only consumer family.
------------------------------------------------------------------------

declaredMatrixConsumer :
  Declared.DeclaredObserverRowSlot ->
  Fabric.Ternary27Point ->
  Observer.ObserverMatrix3 SSP.SSPTrit
declaredMatrixConsumer = Declared.embedDeclaredRow

declaredFabricConsumer :
  Declared.DeclaredObserverRowSlot ->
  Fabric.Ternary27Point ->
  Fabric.TernaryHyperformalPoint
declaredFabricConsumer slot row =
  Bridge.observerToFabric (Declared.embedDeclaredRow slot row)

declaredRubikConsumer :
  Declared.DeclaredObserverRowSlot ->
  Fabric.Ternary27Point ->
  Hyper.AxisBlock 3
declaredRubikConsumer slot row =
  Rubik.rowToRank3Block
    (Declared.selectedRow slot (Declared.embedDeclaredRow slot row))

------------------------------------------------------------------------
-- 2. Generic upstream routing.
------------------------------------------------------------------------

matrixFactorsThroughSurface :
  {State : Set} ->
  (surface : State -> Fabric.Ternary27Point) ->
  (slot : Declared.DeclaredObserverRowSlot) ->
  Descent.FactorsThrough
    surface
    (λ state -> declaredMatrixConsumer slot (surface state))
matrixFactorsThroughSurface surface slot =
  Factorized.factorizedRefinement
    (declaredMatrixConsumer slot)
    (λ state -> refl)

fabricFactorsThroughSurface :
  {State : Set} ->
  (surface : State -> Fabric.Ternary27Point) ->
  (slot : Declared.DeclaredObserverRowSlot) ->
  Descent.FactorsThrough
    surface
    (λ state -> declaredFabricConsumer slot (surface state))
fabricFactorsThroughSurface surface slot =
  Factorized.factorizedRefinement
    (declaredFabricConsumer slot)
    (λ state -> refl)

rubikFactorsThroughSurface :
  {State : Set} ->
  (surface : State -> Fabric.Ternary27Point) ->
  (slot : Declared.DeclaredObserverRowSlot) ->
  Descent.FactorsThrough
    surface
    (λ state -> declaredRubikConsumer slot (surface state))
rubikFactorsThroughSurface surface slot =
  Factorized.factorizedRefinement
    (declaredRubikConsumer slot)
    (λ state -> refl)

matrixSurfaceSufficient :
  {State : Set} ->
  (surface : State -> Fabric.Ternary27Point) ->
  (slot : Declared.DeclaredObserverRowSlot) ->
  Descent.ConsumerSufficient
    surface
    (λ state -> declaredMatrixConsumer slot (surface state))
matrixSurfaceSufficient surface slot =
  Descent.factorsThroughImpliesFibreConstant
    (matrixFactorsThroughSurface surface slot)

fabricSurfaceSufficient :
  {State : Set} ->
  (surface : State -> Fabric.Ternary27Point) ->
  (slot : Declared.DeclaredObserverRowSlot) ->
  Descent.ConsumerSufficient
    surface
    (λ state -> declaredFabricConsumer slot (surface state))
fabricSurfaceSufficient surface slot =
  Descent.factorsThroughImpliesFibreConstant
    (fabricFactorsThroughSurface surface slot)

rubikSurfaceSufficient :
  {State : Set} ->
  (surface : State -> Fabric.Ternary27Point) ->
  (slot : Declared.DeclaredObserverRowSlot) ->
  Descent.ConsumerSufficient
    surface
    (λ state -> declaredRubikConsumer slot (surface state))
rubikSurfaceSufficient surface slot =
  Descent.factorsThroughImpliesFibreConstant
    (rubikFactorsThroughSurface surface slot)

------------------------------------------------------------------------
-- 3. Exact selected-row recovery shows geometric embedding adds no further
-- loss beyond the upstream surface projection.
------------------------------------------------------------------------

selectedRowAfterSurfaceEmbedding :
  {State : Set} ->
  (surface : State -> Fabric.Ternary27Point) ->
  (slot : Declared.DeclaredObserverRowSlot) ->
  (state : State) ->
  Declared.selectedRow slot
    (declaredMatrixConsumer slot (surface state))
  ≡ surface state
selectedRowAfterSurfaceEmbedding surface slot state =
  Declared.selectedRowAfterEmbedding slot (surface state)

fabricProjectionAfterSurfaceEmbedding :
  {State : Set} ->
  (surface : State -> Fabric.Ternary27Point) ->
  (slot : Declared.DeclaredObserverRowSlot) ->
  (state : State) ->
  Declared.fabricProjectionAtSlot slot
    (declaredFabricConsumer slot (surface state))
  ≡ surface state
fabricProjectionAfterSurfaceEmbedding surface slot state =
  Declared.declaredRowHyperformProjectionCommutes slot (surface state)

------------------------------------------------------------------------
-- 4. Consumer contract for an upstream lane.
------------------------------------------------------------------------

record UpstreamT3ConsumerContract (State : Set) : Set₁ where
  field
    surface : State -> Fabric.Ternary27Point

    -- Optional fine consumer supplied by the upstream lane.
    FineOutcome : Set
    fineConsumer : State -> FineOutcome

    -- Proof that the fine consumer really requires information beyond T^3.
    fineConsumerDoesNotDescend :
      Descent.ConsumerSufficient surface fineConsumer -> ⊥

open UpstreamT3ConsumerContract public

record Trialectic369SurfaceConsumerRoutingBoundary : Set where
  constructor trialectic-369-surface-consumer-routing-boundary
  field
    declaredMatrixConsumesOnlyT3 : Bool
    hyperfabricConsumesOnlyT3 : Bool
    rubikBlockConsumesOnlyT3 : Bool
    selectedRowRecoveryExact : Bool
    fabricProjectionRecoveryExact : Bool
    upstreamFineConsumersAutomaticallyDescend : Bool
    upstreamParticipantSemanticIdentityAsserted : Bool

canonicalTrialectic369SurfaceConsumerRoutingBoundary :
  Trialectic369SurfaceConsumerRoutingBoundary
canonicalTrialectic369SurfaceConsumerRoutingBoundary =
  trialectic-369-surface-consumer-routing-boundary
    true true true true true
    false false
