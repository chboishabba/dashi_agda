module DASHI.Reasoning.Trialectic369DeclaredRowConsumerExact where

------------------------------------------------------------------------
-- DECLARED T^3 ROW -> TRIALECTIC T^9 / HYPERFABRIC CONSUMER
--
-- DASHI CONTRIBUTION
--
-- This is the reciprocal seam for any upstream producer that can supply one
-- existing Ternary27Point without claiming relational semantics.
--
-- A producer must explicitly choose which observer row slot receives the
-- T^3 value.  The other two rows are filled with the neutral origin.  The
-- selected row reopens exactly, and the corresponding hyperfabric projection
-- commutes definitionally.
--
-- This module does NOT identify the upstream semantics with participant A/B/C.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as Bridge
import DASHI.Reasoning.Trialectic369RubikRefinementExact as Rubik

data DeclaredObserverRowSlot : Set where
  rowSlotA : DeclaredObserverRowSlot
  rowSlotB : DeclaredObserverRowSlot
  rowSlotC : DeclaredObserverRowSlot

neutralRow : Fabric.Ternary27Point
neutralRow = Fabric.origin

embedDeclaredRow :
  DeclaredObserverRowSlot ->
  Fabric.Ternary27Point ->
  Observer.ObserverMatrix3 SSP.SSPTrit
embedDeclaredRow rowSlotA row =
  Observer.observerMatrix3
    (Fabric.x row) (Fabric.y row) (Fabric.z row)
    SSP.sspZero SSP.sspZero SSP.sspZero
    SSP.sspZero SSP.sspZero SSP.sspZero
embedDeclaredRow rowSlotB row =
  Observer.observerMatrix3
    SSP.sspZero SSP.sspZero SSP.sspZero
    (Fabric.x row) (Fabric.y row) (Fabric.z row)
    SSP.sspZero SSP.sspZero SSP.sspZero
embedDeclaredRow rowSlotC row =
  Observer.observerMatrix3
    SSP.sspZero SSP.sspZero SSP.sspZero
    SSP.sspZero SSP.sspZero SSP.sspZero
    (Fabric.x row) (Fabric.y row) (Fabric.z row)

selectedRow :
  DeclaredObserverRowSlot ->
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  Fabric.Ternary27Point
selectedRow rowSlotA matrix = Bridge.observerRowA matrix
selectedRow rowSlotB matrix = Bridge.observerRowB matrix
selectedRow rowSlotC matrix = Bridge.observerRowC matrix

selectedRowAfterEmbedding :
  (slot : DeclaredObserverRowSlot) ->
  (row : Fabric.Ternary27Point) ->
  selectedRow slot (embedDeclaredRow slot row) ≡ row
selectedRowAfterEmbedding rowSlotA (Fabric.ternary27Point x y z) = refl
selectedRowAfterEmbedding rowSlotB (Fabric.ternary27Point x y z) = refl
selectedRowAfterEmbedding rowSlotC (Fabric.ternary27Point x y z) = refl

fabricProjectionAtSlot :
  DeclaredObserverRowSlot ->
  Fabric.TernaryHyperformalPoint ->
  Fabric.Ternary27Point
fabricProjectionAtSlot rowSlotA fabric = Fabric.interactionVoxel fabric
fabricProjectionAtSlot rowSlotB fabric = Fabric.appraisalAVoxel fabric
fabricProjectionAtSlot rowSlotC fabric = Fabric.appraisalBVoxel fabric

declaredRowHyperformProjectionCommutes :
  (slot : DeclaredObserverRowSlot) ->
  (row : Fabric.Ternary27Point) ->
  fabricProjectionAtSlot slot
    (Bridge.observerToFabric (embedDeclaredRow slot row))
  ≡ row
declaredRowHyperformProjectionCommutes
  rowSlotA (Fabric.ternary27Point x y z) = refl
declaredRowHyperformProjectionCommutes
  rowSlotB (Fabric.ternary27Point x y z) = refl
declaredRowHyperformProjectionCommutes
  rowSlotC (Fabric.ternary27Point x y z) = refl

declaredRowRubikBlockCommutes :
  (slot : DeclaredObserverRowSlot) ->
  (row : Fabric.Ternary27Point) ->
  Rubik.rowToRank3Block
    (selectedRow slot (embedDeclaredRow slot row))
  ≡ Rubik.rowToRank3Block row
declaredRowRubikBlockCommutes slot row =
  cong Rubik.rowToRank3Block (selectedRowAfterEmbedding slot row)

------------------------------------------------------------------------
-- The chosen row position is presentation data.
------------------------------------------------------------------------

data UpstreamT3SemanticsEqualsParticipantRole : Set where
data ChoosingRowAIsCanonicalWithoutCalibration : Set where
data NeutralPaddingMeansAbsentParticipants : Set where

upstreamT3DoesNotAutomaticallyEqualParticipantRole :
  UpstreamT3SemanticsEqualsParticipantRole -> ⊥
upstreamT3DoesNotAutomaticallyEqualParticipantRole ()

rowAChoiceIsNotCanonicalWithoutCalibration :
  ChoosingRowAIsCanonicalWithoutCalibration -> ⊥
rowAChoiceIsNotCanonicalWithoutCalibration ()

neutralPaddingIsChartPaddingNotParticipantAbsence :
  NeutralPaddingMeansAbsentParticipants -> ⊥
neutralPaddingIsChartPaddingNotParticipantAbsence ()

record Trialectic369DeclaredRowConsumerBoundary : Set where
  constructor trialectic-369-declared-row-consumer-boundary
  field
    existingT3CarrierConsumedDirectly : Bool
    rowSlotMustBeDeclared : Bool
    selectedRowReopensExactly : Bool
    hyperfabricProjectionCommutes : Bool
    rubikRank3BlockCommutes : Bool
    upstreamSemanticsIdentifiedWithParticipantRole : Bool
    rowAChoiceCanonicalWithoutCalibration : Bool
    neutralPaddingMeansAbsentParticipants : Bool

canonicalTrialectic369DeclaredRowConsumerBoundary :
  Trialectic369DeclaredRowConsumerBoundary
canonicalTrialectic369DeclaredRowConsumerBoundary =
  trialectic-369-declared-row-consumer-boundary
    true true true true true
    false false false
