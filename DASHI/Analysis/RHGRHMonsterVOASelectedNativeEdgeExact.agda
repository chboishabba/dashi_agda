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
open import Relation.Binary.PropositionalEquality using (sym)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Integer using (ℤ)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact as Axis
import DASHI.Moonshine.Monster27VOACubeWeightedChargeNoGoExact as Charge
import DASHI.Moonshine.Monster27VOAVertexModeChargeSelectionExact as VOA
import DASHI.Moonshine.Monster27VOAOnsiteCube369BridgeExact as Parent
import DASHI.Algebra.TriadicFiniteArithmetic as Arith

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

-- Five independently supplied scalar labels are not substituted for
-- the genuine five-coordinate indexed cube source on unmerged #1291.
-- This theorem is parameter-independent, NOT an Index record theorem.
selectedEdgeAtEveryIndex :
  (h t k j v : Nat) →
  Cube.HypervoxelAdjacent
    (Axis.representative Axis.axisX)
    (Axis.representative Axis.faceXYpp)
selectedEdgeAtEveryIndex h t k j v = selectedNativeXYEdge

noGlobalOrientationAtFiveLabels :
  (h t k j v : Nat) →
  (x pp y pm : Bool) →
  Axis._xor_ x pp ≡ false →
  Axis._xor_ pp y ≡ false →
  Axis._xor_ y pm ≡ true →
  Axis._xor_ pm x ≡ false → ⊥
noGlobalOrientationAtFiveLabels h t k j v =
  Axis.noEdgeCompatibleOrientation

-- The SOURCE-LITERAL selected VOA edge operator is only present once
-- Parent.Monster27VOAOnCubeSource and
-- VOA.LiteralMonster27ModeChargeReceipt are actually inhabited.
-- Those original record types already demand same-group 27th/9th
-- powers, same literal V-natural carrier, actual mode action and
-- a charge-additive output. No standalone Fin27 "operator" is added.

-- A genuine, precisely source-typed CONDITIONAL result: if the
-- original selected literal VOA sector/mode receipt is inhabited,
-- its own mode-output witness lands in the charge of the chosen
-- geometrically native adjacent endpoint. This does NOT populate the
-- receipt, assert nonzero output, or invent a spectral state.
selectedEdgeActualVOAModeOutputSector :
  ∀ {Monster K : Set} →
  (source : Parent.Monster27VOAOnCubeSource Monster K) →
  (receipt : VOA.LiteralMonster27ModeChargeReceipt source) →
  (u : VOA.Sector receipt
    (Charge.chargeLabel (Axis.representative Axis.axisX))) →
  (v : VOA.Sector receipt VOA.positiveYCharge) →
  (n : ℤ) →
  VOA.Sector receipt
    (Charge.chargeLabel (Axis.representative Axis.faceXYpp))
selectedEdgeActualVOAModeOutputSector source receipt u v n
  rewrite sym selectedXYEdgeChargeIncrement =
  proj₁ (VOA.actualVOAModeChargeOutput receipt
    (Charge.chargeLabel (Axis.representative Axis.axisX))
    VOA.positiveYCharge u v n)
