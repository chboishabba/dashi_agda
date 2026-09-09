module DASHI.Moonshine.JInvariantFormulaic369FibreObserverRepairExact where

------------------------------------------------------------------------
-- FORMULAIC 369 RENDERER: SAME-POINT FIBRE OBSERVER REPAIR
--
-- The original renderer correctly retained the continuous phase, but exposed
-- all finite observers as functions of Phase alone.  After the colour-wheel /
-- 9-sheet / pants weld, this is too weak for 9 and 27:
--
--   9 = phase trit x seam/context trit
--
-- and seam/context is not in general recoverable from hue/phase alone.
--
-- This module is a refinement adapter, not a parallel renderer.  It reuses the
-- existing formulaic sample for J, phase, tone, colour, C3 and C6, while
-- replacing only the 9/27 observation seam by same-point fibre observers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein

record SamePointFibreObservers (R : Render.JPhaseRenderingAlgebra) : Set₁ where
  constructor same-point-fibre-observers
  field
    observer9At :
      Klein.Point (Render.klein R) →
      Triadic.NineSheet

    observer27At :
      Klein.Point (Render.klein R) →
      Fabric.Ternary27Point

open SamePointFibreObservers public

record J369FibreRenderSample
  (R : Render.JPhaseRenderingAlgebra)
  (F : SamePointFibreObservers R) : Set where
  constructor j369-fibre-render-sample
  field
    baseSample : Render.J369RenderSample R
    fibreObserver9 : Triadic.NineSheet
    fibreObserver27 : Fabric.Ternary27Point

open J369FibreRenderSample public

renderFibreAt :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : SamePointFibreObservers R) →
  (z : Klein.Point (Render.klein R)) →
  J369FibreRenderSample R F
renderFibreAt R F z =
  j369-fibre-render-sample
    (Render.renderAt R z)
    (observer9At F z)
    (observer27At F z)

------------------------------------------------------------------------
-- The analytic payload and phase-derived 3/6 observers are untouched.
------------------------------------------------------------------------

fibreRepairRetainsExactPhase :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : SamePointFibreObservers R) →
  (z : Klein.Point (Render.klein R)) →
  Render.exactPhase (baseSample (renderFibreAt R F z)) ≡ Render.jPhase R z
fibreRepairRetainsExactPhase R F z = refl

fibreRepairRetainsObserver3 :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : SamePointFibreObservers R) →
  (z : Klein.Point (Render.klein R)) →
  Render.observer3 (baseSample (renderFibreAt R F z))
  ≡ Render.phase3 R (Render.jPhase R z)
fibreRepairRetainsObserver3 R F z = refl

fibreRepairRetainsObserver6 :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : SamePointFibreObservers R) →
  (z : Klein.Point (Render.klein R)) →
  Render.observer6 (baseSample (renderFibreAt R F z))
  ≡ Render.phase6 R (Render.jPhase R z)
fibreRepairRetainsObserver6 R F z = refl

------------------------------------------------------------------------
-- Compatibility with the old phase-only 9/27 fields is explicit, not assumed.
------------------------------------------------------------------------

record LegacyFibreObserverCompatibility
  (R : Render.JPhaseRenderingAlgebra)
  (F : SamePointFibreObservers R) : Set₁ where
  constructor legacy-fibre-observer-compatibility
  field
    nineAgrees :
      (z : Klein.Point (Render.klein R)) →
      observer9At F z ≡ Render.phase9 R (Render.jPhase R z)

    twentySevenAgrees :
      (z : Klein.Point (Render.klein R)) →
      observer27At F z ≡ Render.phase27 R (Render.jPhase R z)

open LegacyFibreObserverCompatibility public

record FibreObserverRepairBoundary : Set where
  constructor fibre-observer-repair-boundary
  field
    continuousPhaseStillRetained : Bool
    c3StillPhaseObserver : Bool
    c6StillPhaseOrientationObserver : Bool
    c9MayDependOnSamePointContext : Bool
    c27MayDependOnSamePointContext : Bool
    seamForcedToBeFunctionOfHue : Bool
    legacyPhaseOnlyAgreementAutomatic : Bool

canonicalFibreObserverRepairBoundary : FibreObserverRepairBoundary
canonicalFibreObserverRepairBoundary =
  fibre-observer-repair-boundary
    true true true true true false false
