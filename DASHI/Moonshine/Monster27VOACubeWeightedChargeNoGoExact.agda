module DASHI.Moonshine.Monster27VOACubeWeightedChargeNoGoExact where

-- Canonical geometry = genuine balanced ternary 3x3x3 Cube27.
-- Spectral charge is SEPARATE: g of Monster 27A/B on Vnatural_2.
-- PRIMARY EXTERNAL SOURCE ROOTS:
-- FLM Vnatural_2=1+196883 rational character;
-- ATLAS 27A/B^3 in 9B and 27A/B^9 in 3B;
-- Conway-Norton/Ford-McKay-Norton/OEIS T_27=q^-1+3q+...,
-- T_9B=q^-1+0q+5q²+..., T_3B=q^-1+54q-76q²+...
-- Invert rational C27 character via Ramanujan sums:
-- multiplicity for roots of exact orders 1,3,9,27 =
-- 7298, 7295, 7296, 7290 per eigenvalue respectively.
-- This establishes a CHOSEN 27-charge-label <-> 27-cube digit chart,
-- not natural adjacency, VOA product, or a lattice Hamiltonian.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Moonshine.JInvariant369Cube27CuspCodecNonIsometryExact as Codec

-- The EXISTING cube site coordinates are also an exact invertible
-- balanced-digit chart on the 27 cyclic eigencharge labels.
chargeLabel : Cube.Ternary27Point → Q.Residue3Pow 3
chargeLabel = Codec.encodeCubeDigits

-- Multiplicities fixed by the three ACTUAL Monster trace coefficients.
-- The physical 196884-space is a direct sum of these 27 eigenspaces;
-- actual linear eigenspaces require the existing selected-VOA authority
-- in Monster27VOAOnsiteCube369BridgeExact, not fake Fin states.
chargeFibreRank : Cube.Ternary27Point → Nat
chargeFibreRank (Cube.ternary27Point SSP.sspNegOne y z) = 7290
chargeFibreRank (Cube.ternary27Point SSP.sspPosOne y z) = 7290
chargeFibreRank (Cube.ternary27Point SSP.sspZero SSP.sspNegOne z) = 7296
chargeFibreRank (Cube.ternary27Point SSP.sspZero SSP.sspPosOne z) = 7296
chargeFibreRank (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = 7295
chargeFibreRank (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = 7295
chargeFibreRank (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = 7298

centreRank : chargeFibreRank Cube.origin ≡ 7298
centreRank = refl

cornerRank : chargeFibreRank Cube.positiveCorner ≡ 7290
cornerRank = refl

positiveZAxisRank :
  chargeFibreRank
    (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne)
  ≡ 7295
positiveZAxisRank = refl

positiveYPlaneRank :
  chargeFibreRank
    (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero)
  ≡ 7296
positiveYPlaneRank = refl

-- Exact aggregate: 1 centre, 2 z-axis, 6 x=0 off-axis,
-- and 18 x=+/-1 face points.
fullMonsterWeightTwoCount :
  7298 + (2 * 7295) + (6 * 7296) + (18 * 7290)
  ≡ 196884
fullMonsterWeightTwoCount = refl

primitivePartDimension : 18 * 7290 ≡ 131220
primitivePartDimension = refl

existing3BModelSplit : 9 * 7290 ≡ 729 * 90
existing3BModelSplit = refl

threeBTracesRecovered :
  7298 + (2 * 7295) + (6 * 7296) ≡ 65664
threeBTracesRecovered = refl

-- STRUCTURAL NO-GO: every nearest-neighbour *spatial cube* edge
-- joins TWO DIFFERENT cyclic charge labels under this chosen chart.
-- Therefore a charge-preserving block-diagonal hopping operator cannot
-- have ANY bare offdiagonal edge hopping between these eigenspaces.
-- A compensating charged link (gauge field) is a distinct extra object.
edgeEndpointsHaveDifferentCharge :
  ∀ {p q} →
  Cube.HypervoxelAdjacent p q →
  chargeLabel p ≡ chargeLabel q → ⊥
edgeEndpointsHaveDifferentCharge (Cube.adjacentX Cube.negToZero) ()
edgeEndpointsHaveDifferentCharge (Cube.adjacentX Cube.zeroToNeg) ()
edgeEndpointsHaveDifferentCharge (Cube.adjacentX Cube.zeroToPos) ()
edgeEndpointsHaveDifferentCharge (Cube.adjacentX Cube.posToZero) ()
edgeEndpointsHaveDifferentCharge (Cube.adjacentY Cube.negToZero) ()
edgeEndpointsHaveDifferentCharge (Cube.adjacentY Cube.zeroToNeg) ()
edgeEndpointsHaveDifferentCharge (Cube.adjacentY Cube.zeroToPos) ()
edgeEndpointsHaveDifferentCharge (Cube.adjacentY Cube.posToZero) ()
edgeEndpointsHaveDifferentCharge (Cube.adjacentZ Cube.negToZero) ()
edgeEndpointsHaveDifferentCharge (Cube.adjacentZ Cube.zeroToNeg) ()
edgeEndpointsHaveDifferentCharge (Cube.adjacentZ Cube.zeroToPos) ()
edgeEndpointsHaveDifferentCharge (Cube.adjacentZ Cube.posToZero) ()

record ChargePreservingOffDiagonalBond
  (Bond : Cube.Ternary27Point → Cube.Ternary27Point → Set) : Set where
  field
    chargePreservation :
      (p q : Cube.Ternary27Point) →
      Bond p q → chargeLabel p ≡ chargeLabel q
open ChargePreservingOffDiagonalBond public

noNonzeroNearestNeighbourBond :
  ∀ {Bond : Cube.Ternary27Point → Cube.Ternary27Point → Set}
  (charge : ChargePreservingOffDiagonalBond Bond)
  {p q : Cube.Ternary27Point} →
  Cube.HypervoxelAdjacent p q →
  Bond p q → ⊥
noNonzeroNearestNeighbourBond charge {p} {q} edge bond =
  edgeEndpointsHaveDifferentCharge edge
    (chargePreservation charge p q bond)

-- CRITICAL ALTERNATIVE: when every REAL geometric site carries a COPY
-- of the whole VOA weight-two representation, all sites can carry the
-- SAME g action and spatial hopping can preserve it. That is the
-- distinct product construction in Monster27VOAOnsiteCube369BridgeExact.
-- No claim that an algebraic chart produces geometric adjacency.
