module DASHI.Interop.AdicHypervoxelArgumentTransportBridgeExact where

------------------------------------------------------------------------
-- ADIC / HYPERVOXEL / BT-BRAID TRANSPORT CROSS-POLLINATION
--
-- The existing geometry core represents a refinement by a BT-braid strand
-- whose source is the current hypervoxel cell and whose target is the refined
-- cell.  Its Young-Fibonacci relation is explicitly a projected shadow, not a
-- definitional identity.
--
-- This is the geometric analogue of argument-level transport: refinement may
-- change chart/cell while a typed transport relation keeps the source/target
-- dependency explicit.  The analogy does not identify semantic arguments with
-- adic points or physical/geometric carriers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Geometry.HypervoxelAdicYoungFibonacciBridge as Adic
import DASHI.Core.ArgumentLevelTransportHyperformalismExact as Argument

adicBridgeRemainsProjectedShadow :
  ∀ {H A B G S} →
  (bridge : Adic.HypervoxelAdicYoungFibonacciBridge H A B G S) →
  Adic.HypervoxelAdicYoungFibonacciBridge.relation bridge
  ≡ Adic.projectedShadow
adicBridgeRemainsProjectedShadow =
  Adic.bridge-not-asserted-as-identity

record AdicArgumentTransportBoundary : Set where
  constructor adicArgumentTransportBoundary
  field
    refinementNeedsTypedSourceTarget : Bool
    projectedShadowEqualsDefinitionalIdentity : Bool
    argumentCarrierEqualsAdicPoint : Bool
    projectionDisciplineCrossPollinates : Bool

canonicalAdicArgumentTransportBoundary : AdicArgumentTransportBoundary
canonicalAdicArgumentTransportBoundary =
  adicArgumentTransportBoundary true false false true
