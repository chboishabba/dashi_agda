{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPreferredCanonicalCMP109SourceS4NoGoExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityCMP109CanonicalSU2FiniteHistoryExact as CanonicalFinite
import DASHI.Physics.Foundations.CMP119AntigravityCMP109PlaquetteFiniteHistoryExact as FiniteHistory
import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceCouplingCoordinateExact as SourceCoupling
import DASHI.Physics.Foundations.CMP119AntigravityA2CMP109SourceCouplingExact as A2Source
import DASHI.Physics.Foundations.CMP119AntigravityA2CMP109SourceTerminalGeometryExact as A2Geometry
import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceRowABetaDrivenDensityExact as Density
import DASHI.Physics.Foundations.CMP119AntigravityPreferredCMP109SourceS4NoGoExact as Preferred
import DASHI.Physics.Foundations.CMP119AntigravityUnifiedA2RowACapExact as Unified
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as Convention
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SHORTEST CURRENT SOURCE-OWNED S4 PACKAGE
--
-- The finite beta history is now compiled from:
--
--   * one literal CMP109 beta/coefficient weld;
--   * one SU(2) log window;
--   * one coefficient-side quartic enclosure per edge.
--
-- The terminal small-coupling history is separately compiled from:
--
--   * the primary CMP109 source coupling;
--   * one early A2 = CMP109 source-coupling weld;
--   * terminal prefix geometry.
--
-- Thus coefficient-side and physical source coupling remain distinct objects.
------------------------------------------------------------------------

record PreferredCanonicalCMP109SourceS4NoGo
    {HistoryCarrier Cell : Set}
    {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory)
    (finiteSource : CanonicalFinite.CMP109CanonicalSU2FiniteHistory weld)
    (sourceCoupling : SourceCoupling.CMP109SourceCouplingCoordinate trajectory)
    (a2Coupling :
      A2Source.A2CMP109SourceCouplingCoordinate present sourceCoupling)
    (geometry :
      A2Geometry.A2CMP109SourceTerminalGeometry
        present
        (CanonicalFinite.asCMP109PlaquetteFiniteHistory finiteSource)
        sourceCoupling
        a2Coupling) : Set₂ where
  field
    density :
      Density.CMP109SourceRowABetaDrivenDensity
        (CanonicalFinite.asCMP109PlaquetteFiniteHistory finiteSource)
        sourceCoupling
        (Unified.rowAConstantsFromA2 present)
        (A2Geometry.asCMP109SourceRowATerminalGeometry geometry)

    traceBoundary :
      Convention.CanonicalBishopSU2TraceBoundary

open PreferredCanonicalCMP109SourceS4NoGo public

asPreferredCMP109SourceS4NoGo :
  ∀ {HistoryCarrier Cell cutoff present trajectory weld finiteSource sourceCoupling a2Coupling geometry} →
  PreferredCanonicalCMP109SourceS4NoGo
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present trajectory weld finiteSource sourceCoupling a2Coupling geometry →
  Preferred.PreferredCMP109SourceS4NoGo
    present
    trajectory
    weld
    (CanonicalFinite.asCMP109PlaquetteFiniteHistory finiteSource)
    sourceCoupling
    a2Coupling
    geometry
asPreferredCMP109SourceS4NoGo package = record
  { Preferred.PreferredCMP109SourceS4NoGo.density =
      density package
  ; Preferred.PreferredCMP109SourceS4NoGo.traceBoundary =
      traceBoundary package
  }

freeFiniteBetaCertificatesRequired : Bool
freeFiniteBetaCertificatesRequired = false

freeUniformGaussianBoundsRequired : Bool
freeUniformGaussianBoundsRequired = false

freeCoefficientCouplingRequired : Bool
freeCoefficientCouplingRequired = false

freeFiniteBetaCertificatesRequiredIsFalse :
  freeFiniteBetaCertificatesRequired ≡ false
freeFiniteBetaCertificatesRequiredIsFalse = refl

freeUniformGaussianBoundsRequiredIsFalse :
  freeUniformGaussianBoundsRequired ≡ false
freeUniformGaussianBoundsRequiredIsFalse = refl

freeCoefficientCouplingRequiredIsFalse :
  freeCoefficientCouplingRequired ≡ false
freeCoefficientCouplingRequiredIsFalse = refl

preferredCanonicalCMP109SourceS4CompilerLevel : ProofLevel
preferredCanonicalCMP109SourceS4CompilerLevel = machineChecked

------------------------------------------------------------------------
-- Surviving source/provenance leaves:
--
--   S4-P1  source beta_(k+1) = literal one-loop + remainder coefficient;
--   S4-P2  one finite SU(2) log window;
--   S4-P3  coefficient-side signed O(g^4) remainder / half-gap per edge;
--   S4-P4  primary CMP109 source coupling meaning u_k g_k^2 = 1;
--   S4-P5  A2 coupling = that same CMP109 source coupling;
--   S4-P6  terminal scale belongs to the A2 finite prefix / active geometry;
--   S4-P7  CMP119/CMP122 density/Section-2 realization;
--   S4-P8  selected Lorentzian trace/F^2 boundary.
--
-- All scalar threshold arithmetic, cap selection, pi normalization, Gaussian
-- history packaging, certificate-coupling choice and terminal threshold order
-- are compiler-owned.
------------------------------------------------------------------------
