{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPreferredA2CanonicalSU2S4NoGoExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalSU2LiteralHistoryExact as SU2History
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as CanonicalHistory
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowAInverseThresholdExact as Threshold
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowALiteralTerminalHistoryExact as Terminal
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteBetaDrivenDensityExact as Density
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as Convention
import DASHI.Physics.Foundations.CMP119AntigravityPreferredCanonicalSU2S4NoGoExact as Preferred
import DASHI.Physics.Foundations.CMP119AntigravityA2LiteralCouplingCoordinateExact as A2Literal
import DASHI.Physics.Foundations.CMP119AntigravityA2LiteralTerminalGeometryExact as A2Geometry
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowACouplingBoundGeometryExact as Geometry
import DASHI.Physics.Foundations.CMP119AntigravityUnifiedA2RowACapExact as Unified
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PREFERRED A2-NATIVE S4 PACKAGE
--
-- There is no free Row-A numeric package on this route.
--
--   present.a2
--      -> producer Ward constants
--      -> canonical FiniteQuarticResponseConstants
--      -> canonical gamma
--      -> exact reciprocal inverse threshold
--
-- and the SAME present.a2 coupling is welded to the literal plaquette coupling
-- before CMP122 packaging.  Thus Row-A cap, literal coupling, terminal
-- threshold and beta-driven density all share one provenance spine.
------------------------------------------------------------------------

record PreferredA2CanonicalSU2S4NoGo
    {HistoryCarrier Cell : Set}
    {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff)
    (plaquette : Plaquette.PhysicalRunningCouplingData Nat)
    (coherence : Source.LiteralPlaquetteUVChainCoherence plaquette)
    (source : SU2History.CanonicalSU2LiteralHistory plaquette coherence)
    (coordinate : A2Literal.A2LiteralCouplingCoordinate present plaquette)
    (geometry :
      A2Geometry.A2LiteralTerminalGeometry
        present plaquette coherence
        (SU2History.asCanonicalLiteralPlaquetteHistory source)
        coordinate) : Set₂ where
  field
    density :
      Density.LiteralPlaquetteBetaDrivenDensity
        plaquette
        (CanonicalHistory.trajectory coherence)
        (CanonicalHistory.asLiteralPlaquetteCMP109FiniteHistory
          (SU2History.asCanonicalLiteralPlaquetteHistory source))
        (Terminal.asLiteralPlaquetteTerminalHistory
          (Threshold.asCanonicalRowALiteralTerminalHistory
            (Geometry.asCanonicalRowATerminalGeometry
              (A2Geometry.asCanonicalRowACouplingBoundGeometry geometry))))

    traceBoundary :
      Convention.CanonicalBishopSU2TraceBoundary

open PreferredA2CanonicalSU2S4NoGo public

asPreferredCanonicalSU2S4NoGo :
  ∀ {HistoryCarrier Cell cutoff present plaquette coherence source coordinate geometry} →
  PreferredA2CanonicalSU2S4NoGo
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present plaquette coherence source coordinate geometry →
  Preferred.PreferredCanonicalSU2S4NoGo
    plaquette coherence source
    (Unified.rowAConstantsFromA2 present)
    (A2Geometry.asCanonicalRowACouplingBoundGeometry geometry)
asPreferredCanonicalSU2S4NoGo package = record
  { Preferred.PreferredCanonicalSU2S4NoGo.density =
      density package
  ; Preferred.PreferredCanonicalSU2S4NoGo.traceBoundary =
      traceBoundary package
  }

freeRowAConstantsRequired : Bool
freeRowAConstantsRequired = false

freeRowACouplingCapRequired : Bool
freeRowACouplingCapRequired = false

freeTerminalCouplingCapRequired : Bool
freeTerminalCouplingCapRequired = false

freeTerminalInverseThresholdRequired : Bool
freeTerminalInverseThresholdRequired = false

freeRowAConstantsRequiredIsFalse :
  freeRowAConstantsRequired ≡ false
freeRowAConstantsRequiredIsFalse = refl

freeRowACouplingCapRequiredIsFalse :
  freeRowACouplingCapRequired ≡ false
freeRowACouplingCapRequiredIsFalse = refl

freeTerminalCouplingCapRequiredIsFalse :
  freeTerminalCouplingCapRequired ≡ false
freeTerminalCouplingCapRequiredIsFalse = refl

freeTerminalInverseThresholdRequiredIsFalse :
  freeTerminalInverseThresholdRequired ≡ false
freeTerminalInverseThresholdRequiredIsFalse = refl

preferredA2CanonicalSU2S4CompilerLevel : ProofLevel
preferredA2CanonicalSU2S4CompilerLevel = machineChecked

------------------------------------------------------------------------
-- Surviving S4 source/provenance leaves on this route:
--
--   1. literal UV-chain coherence;
--   2. one finite SU(2) log window;
--   3. per-step absolute quartic interaction enclosure;
--   4. A2 direct coupling = literal plaquette coupling;
--   5. literal u_k g_k^2 = 1 representation + terminal prefix geometry;
--   6. CMP119/CMP122 density/Section-2 source realization;
--   7. selected Lorentzian trace/F^2 boundary.
--
-- No new scalar inequality, cap choice, pi normalization, or threshold choice
-- remains in S4.
------------------------------------------------------------------------
