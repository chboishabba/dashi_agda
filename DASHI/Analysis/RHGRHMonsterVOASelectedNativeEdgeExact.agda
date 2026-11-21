module DASHI.Analysis.RHGRHMonsterVOASelectedNativeEdgeExact where

-- The first genuine native neighbour edge is an EXISTING P3^3 edge:
-- axisX=(+1,0,0) -> faceXYpp=(+1,+1,0).
-- Source owns both the geometry and the C27 spectral-charge encoding.
-- A selected charged VOA mode is a CONDITIONAL consumer of an original
-- LiteralMonster27ModeChargeReceipt, not an invented vertex operator.
-- The explicit selected four-cycle requires a nontrivial orientation seam.
-- Kernel check OPEN, no CI.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact as Axis
import DASHI.Moonshine.Monster27VOACubeWeightedChargeNoGoExact as Charge
import DASHI.Moonshine.Monster27VOAVertexModeChargeSelectionExact as VOA
import DASHI.Algebra.TriadicFiniteArithmetic as Arith
import DASHI.Analysis.RHGRHIndexedPunctured27HolonomyExact as Index
import DASHI.Moonshine.Monster27VOAOnsiteCube369BridgeExact as Parent

-- This is not a fabricated edge: the original proof term is reused.
selectedNativeXYEdge :
  Cube.HypervoxelAdjacent
    (Axis.representative Axis.axisX)
    (Axis.representative Axis.faceXYpp)
selectedNativeXYEdge = Axis.edgeAxisXFacePP

-- The selected edge's additive charge is the already-defined +Y
-- charge generator in the source's C27 digit chart. The equality is
-- finite balanced-ternary addition on the ORIGINAL residue type.
selectedXYEdgeChargeIncrement :
  Arith.addResidue
    (Charge.chargeLabel (Axis.representative Axis.axisX))
    VOA.positiveYCharge
  ≡ Charge.chargeLabel (Axis.representative Axis.faceXYpp)
selectedXYEdgeChargeIncrement = refl

-- Neither charge endpoint equals the other on this edge.
selectedXYEdgeIsNotNeutral :
  Charge.chargeLabel (Axis.representative Axis.axisX)
    ≡ Charge.chargeLabel (Axis.representative Axis.faceXYpp) → ⊥
selectedXYEdgeIsNotNeutral =
  Charge.edgeEndpointsHaveDifferentCharge selectedNativeXYEdge

selectedStartOrientation :
  Axis.encode (Axis.representative Axis.axisX)
    ≡ just (Axis.axisX , false)
selectedStartOrientation = refl

selectedEndOrientation :
  Axis.encode (Axis.representative Axis.faceXYpp)
    ≡ just (Axis.faceXYpp , false)
selectedEndOrientation = refl

-- This local charge transition has a consistent orientation 0->0.
-- It does not extend to a globally oriented neutral operator:
-- on the source's actual four-cycle one of the four signed edges
-- must flip orientation. No scalar j quotient can erase that seam.
localSelectedEdgeParity :
  Axis._xor_ false false ≡ false
localSelectedEdgeParity = refl

-- An explicit five-axis consumer. There is NO attempt to construct a
-- CubeIndex.ExactFaces proof from a noncommuting native 4-cycle.
selectedEdgeAtEveryIndex :
  (h t k j v : Nat) →
  Cube.HypervoxelAdjacent
    (Axis.representative Axis.axisX)
    (Axis.representative Axis.faceXYpp)
selectedEdgeAtEveryIndex h t k j v = selectedNativeXYEdge

noGlobalOrientationOnAnyIndex :
  (k : Index.AxisIndex) →
  Index.ClaimedGlobalOrientationAt k → ⊥
noGlobalOrientationOnAnyIndex =
  Index.noGlobalEdgeSectionAt

-- The SOURCE-LITERAL selected VOA edge operator is only present once
-- Parent.Monster27VOAOnCubeSource and
-- VOA.LiteralMonster27ModeChargeReceipt are actually inhabited.
-- Those original record types already demand same-group 27th/9th
-- powers, same literal V-natural carrier, actual mode action and
-- a charge-additive output. No standalone Fin27 "operator" is added.
