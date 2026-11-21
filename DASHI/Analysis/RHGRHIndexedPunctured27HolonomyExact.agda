module DASHI.Analysis.RHGRHIndexedPunctured27HolonomyExact where

-- Indexed *native* sign-holonomy obstruction.
-- Reuses EXACT original punctured P3^3 point/edge source #1249 and
-- its 13-axis two-sided oriented carrier and no-global-section theorem.
-- Reuses ORIGINAL governed cube's five-axis index, rather than encoding
-- history/time/depth/Frobenius/version in one Nat.
-- No claim that an arbitrary index transport or six-face cube commutes.
-- No Monster/Hecke/analytic RH promotion; Agda kernel check pending.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just; nothing)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Core.GovernedIndexedResidualCubeExact as CubeIndex
import DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact as Native
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Unified.Hyperfabric27MinusOneAntipodalSameCarrierCutExact as Antipode

-- This source index keeps all five axes; it is not the previous single
-- Nat-time fixture. Residual, sign and observed-zero remain independent
-- fields, rather than being reconstructed from the quotient axis.
AxisIndex : Set
AxisIndex = CubeIndex.Index Nat Nat Nat Nat Nat

record IndexedNativeAxis : Set where
  constructor indexed-native-axis
  field
    index : AxisIndex
    axis : Native.Axis13
    orientation : Bool
    observedZero : Bool
    sign : Bool
    residual : Nat
open IndexedNativeAxis public

-- A native input can be decoded without losing its orientation.
-- Sign, observed zero and residual are *not* inferred from the axis.
decodeIndexedNative : IndexedNativeAxis → Cube.Ternary27Point
decodeIndexedNative x =
  Native.decode (axis x , orientation x)

-- Reusing the source theorem is an actual two-sided codec, even after
-- attaching an independent five-coordinate index and residual ledger.
indexedNativeRoundTrip :
  (x : IndexedNativeAxis) →
  Native.encode (decodeIndexedNative x)
  ≡ just (axis x , orientation x)
indexedNativeRoundTrip x =
  Native.decodeEncode (axis x) (orientation x)

-- The same source antipode flips the recovered orientation. No
-- arbitrary globally consistent choice of graph-edge orientation
-- follows from this exact pointwise roundtrip.
indexedNativeAntipode :
  (x : IndexedNativeAxis) →
  Native.encode (Antipode.antipode (decodeIndexedNative x))
    ≡ just (axis x , Native.flipBit (orientation x))
indexedNativeAntipode x =
  Native.encodeAntipode
    (decodeIndexedNative x)
    (axis x) (orientation x)
    (indexedNativeRoundTrip x)

-- A condition on an actual source-selected four-cycle, not a
-- synthetic commuting-square face; indexed history labels cannot
-- manufacture a missing globally edge-compatible sign section.
record ClaimedGlobalOrientationAt (index : AxisIndex) : Set where
  field
    x : Bool
    pp : Bool
    y : Bool
    pm : Bool
    edgeXPP : Native._xor_ x pp ≡ false
    edgePPY : Native._xor_ pp y ≡ false
    edgeYPM : Native._xor_ y pm ≡ true
    edgePMX : Native._xor_ pm x ≡ false
open ClaimedGlobalOrientationAt public

noGlobalEdgeSectionAt :
  (index : AxisIndex) →
  ClaimedGlobalOrientationAt index → ⊥
noGlobalEdgeSectionAt index witness =
  Native.noEdgeCompatibleOrientation
    (x witness) (pp witness) (y witness) (pm witness)
    (edgeXPP witness) (edgePPY witness)
    (edgeYPM witness) (edgePMX witness)

-- True for every requested physical/refinement/history/consumer index;
-- a seven-axis/Monster "gauge correction" would need actual edge data
-- and a correction law, not the declaration of a symmetry quotient.
noGlobalEdgeSectionAnyFiveAxes :
  (h t k j v : Nat) →
  ClaimedGlobalOrientationAt
    (record
      { history = h
      ; time = t
      ; depth = k
      ; iteration = j
      ; version = v }) → ⊥
noGlobalEdgeSectionAnyFiveAxes h t k j v =
  noGlobalEdgeSectionAt
    (record
      { history = h
      ; time = t
      ; depth = k
      ; iteration = j
      ; version = v })

-- In particular no "observed zero" flag can turn a
-- nontrivial native four-cycle sign into a global section.
