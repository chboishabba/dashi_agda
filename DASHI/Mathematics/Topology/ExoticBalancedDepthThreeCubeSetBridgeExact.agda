module DASHI.Mathematics.Topology.ExoticBalancedDepthThreeCubeSetBridgeExact where

------------------------------------------------------------------------
-- SAME FINITE SET, DISTINCT GEOMETRIC STRUCTURES.
--
-- Source OWNERS, without a new cube or trit implementation:
--   DASHI.Algebra.Trit
--   DASHI.Foundations.SSPTritCarrier.toTrit/fromTrit and roundtrips
--   DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact:
--       original Ternary27Point and origin
--   ExoticBalancedTernaryPantsWeldExact: trit/369/pants addresses
--   TernaryPantsFrontierExact: native 3-way finite branch frontier
--
-- The genuine finite PL two-pants construction in
-- exotic_topology_balanced_ternary_pl.py has exactly 3^3=27
-- outgoing circles at depth 3. Its *labels* Vec Trit 3 and
-- the original 27-point spatial cube are bijective as SETS.
--
-- Crucial negative boundary: this DOES NOT mean that the
-- 2-dimensional oriented surface is homeomorphic to the 3D
-- grid, or that prefix sibling incidence is cube adjacency,
-- the 26 nonzero-point puncture, its antipodal PG13 quotient,
-- a C3-equivariant embedding or a metric/physical identification.
-- Keep every extra structure as an independent obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Mathematics.Topology.ExoticBalancedTernaryPantsWeldExact as Pants

BalancedDepthThree : Set
BalancedDepthThree = Vec Trit.Trit 3

depthThreeToNativeCube : BalancedDepthThree → Cube.Ternary27Point
depthThreeToNativeCube (a vcons b vcons c vcons vnil) =
  Cube.ternary27Point
    (SSP.fromTrit a) (SSP.fromTrit b) (SSP.fromTrit c)

nativeCubeToDepthThree : Cube.Ternary27Point → BalancedDepthThree
nativeCubeToDepthThree (Cube.ternary27Point a b c) =
  SSP.toTrit a vcons SSP.toTrit b vcons SSP.toTrit c vcons vnil

depthThreeCubeRoundTrip :
  (word : BalancedDepthThree) →
  nativeCubeToDepthThree (depthThreeToNativeCube word) ≡ word
depthThreeCubeRoundTrip (a vcons b vcons c vcons vnil)
  rewrite SSP.toTrit-fromTrit a
        | SSP.toTrit-fromTrit b
        | SSP.toTrit-fromTrit c = refl

cubeDepthThreeRoundTrip :
  (point : Cube.Ternary27Point) →
  depthThreeToNativeCube (nativeCubeToDepthThree point) ≡ point
cubeDepthThreeRoundTrip (Cube.ternary27Point a b c)
  rewrite SSP.fromTrit-toTrit a
        | SSP.fromTrit-toTrit b
        | SSP.fromTrit-toTrit c = refl

balancedOriginWord : BalancedDepthThree
balancedOriginWord =
  Trit.zer vcons Trit.zer vcons Trit.zer vcons vnil

balancedOriginIsNativeCubeOrigin :
  depthThreeToNativeCube balancedOriginWord ≡ Cube.origin
balancedOriginIsNativeCubeOrigin = refl

-- A POINT-SET bijection only. In particular the native cube graph's
-- -1 <-> 0 <-> +1 adjacency must NOT be assumed preserved by
-- the rooted pants-tree parent/child incidence.
