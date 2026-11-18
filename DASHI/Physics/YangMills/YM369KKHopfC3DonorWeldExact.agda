module DASHI.Physics.YangMills.YM369KKHopfC3DonorWeldExact where

------------------------------------------------------------------------
-- ATTRIBUTION / PROVENANCE
-- CLASSICAL: Lie SU(2) bracket = 2 times R3 cross product (under the
-- selected quaternion convention); Maxwell U(1) magnetic monopole and
-- Gibbons-Hawking/Gross-Perry-Sorkin KK circle fibration are distinct.
-- EXISTING DASHI: SU2Bracket369OrientationBridgeExact proves three
-- literal bracket-coordinate identities; BalabanCMP109SpatialC3ActionExact
-- proves the original source-grid XYZ cycle; HopfQuaternionAxisProjectionExact
-- proves phase invariance of the SU2 quaternion-axis map.
-- CURRENT DASHI: direct import-based joint proof package, without
-- replacing the native Balaban YM field with an unrelated monopole.
-- RESEARCH DIRECTION: user-proposed 369 YM -> KK/Hopf soliton comparison.
-- ChatGPT-assisted formalization on PR #1531, 2026-11-18.
--
-- RESTRICTION: spatial C3 action and Hopf U1 phase invariance are
-- independently proved on DIFFERENT carriers. No Einstein equation,
-- continuum YM solution, shared connection, Chern number, soliton
-- stability, particle spin, or spin statistics is inferred here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude

import DASHI.Physics.YangMills.SU2Bracket369OrientationBridgeExact as Bracket
import DASHI.Physics.YangMills.BalabanCMP109SpatialC3ActionExact as Spatial
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Lie
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using\n  (_+R_; _*R_; -R_)
import DASHI.Mathematics.Topology.HopfQuaternionAxisProjectionExact as Hopf
import DASHI.Mathematics.Topology.HopfU1CosetOrbitExact as Orbit
import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U1

-- On the actual source-generated four-coordinate Balaban grid,
-- the time coordinate is unchanged while spatial axes cycle.
ym369SourceXYZCycleCubed :
  (cell : Grid.GridCell4) →
  Spatial.spatialCycle123
    (Spatial.spatialCycle123 (Spatial.spatialCycle123 cell)) ≡ cell
ym369SourceXYZCycleCubed = Spatial.spatialCycle123Cubed

-- Original YM source-bracket x-component, without restating its proof.
ym369SourceSU2BracketX :
  ∀ y₁ z₁ y₂ z₂ →
  Lie.bracket1R y₁ z₁ y₂ z₂
  ≡ Lie.twoR *R ((y₁ *R z₂) +R (-R (z₁ *R y₂)))
ym369SourceSU2BracketX = Bracket.su2Bracket1IsTwoCrossMinor

-- On a separate real SU2 quaternion carrier, Hopf's axis projection
-- is invariant under the existing actual U(1) right-phase group action.
hopfPhaseGaugeInvariant :
  (g : Orbit.Total) (u : U1.U1TorusElement) →
  Hopf.axisMap (Orbit.rightPhase g u) ≡ Hopf.axisMap g
hopfPhaseGaugeInvariant = Hopf.canonicalAxisPhaseInvariant

-- A simultaneous nonempty package of EXACT already proved results
-- with no fabricated identification between GridCell4 and Orbit.Total.
record OriginalYM369HopfDonors : Set where
  field
    xyzCycle : (cell : Grid.GridCell4) →
      Spatial.spatialCycle123
        (Spatial.spatialCycle123 (Spatial.spatialCycle123 cell)) ≡ cell
    hopfPhase : (g : Orbit.Total) (u : U1.U1TorusElement) →
      Hopf.axisMap (Orbit.rightPhase g u) ≡ Hopf.axisMap g

canonicalOriginalYM369HopfDonors : OriginalYM369HopfDonors
canonicalOriginalYM369HopfDonors = record
  { xyzCycle = ym369SourceXYZCycleCubed
  ; hopfPhase = hopfPhaseGaugeInvariant
  }
