module DASHI.Moonshine.JInvariantFormulaic369CompactCodecBidiExact where

------------------------------------------------------------------------
-- FORMULAIC J -> SAME-POINT 369 OBSERVERS -> COMPACT CODEC BIDI
--
-- This module applies the existing codec reconciliation to the actual
-- same-point observer repair.  It compresses only the finite observer fibre;
-- the analytic J value, continuous phase, tone and colour remain in the base
-- render sample and are not claimed reconstructible from this finite code.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe using (Maybe; just)

import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369FibreObserverRepairExact as Repair
import DASHI.Moonshine.JInvariant369CodecReconciliationFrontierExact as Compact
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein

record CompactSamePointObserverSample
  (R : Render.JPhaseRenderingAlgebra)
  (F : Repair.SamePointFibreObservers R) : Set where
  constructor compact-same-point-observer-sample
  field
    baseSample : Repair.J369FibreRenderSample R F
    code9 : Compact.NineCompactCode
    code27 : Compact.Compact27

open CompactSamePointObserverSample public

encodeCompactAt :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : Repair.SamePointFibreObservers R) →
  (z : Klein.Point (Render.klein R)) →
  CompactSamePointObserverSample R F
encodeCompactAt R F z =
  compact-same-point-observer-sample
    (Repair.renderFibreAt R F z)
    (Compact.encodeCompactNine (Repair.observer9At F z))
    (Compact.encodeCompact27 (Repair.observer27At F z))

observer9CompactRoundTripAt :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : Repair.SamePointFibreObservers R) →
  (z : Klein.Point (Render.klein R)) →
  Compact.decodeCompactNine (code9 (encodeCompactAt R F z))
  ≡ Repair.observer9At F z
observer9CompactRoundTripAt R F z =
  Compact.decodeEncodeCompactNine (Repair.observer9At F z)

observer27CompactRoundTripAt :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : Repair.SamePointFibreObservers R) →
  (z : Klein.Point (Render.klein R)) →
  Compact.decodeCompact27 (code27 (encodeCompactAt R F z))
  ≡ Repair.observer27At F z
observer27CompactRoundTripAt R F z =
  Compact.decodeEncodeCompact27 (Repair.observer27At F z)

record Formulaic369CompactCodecBoundary : Set where
  constructor formulaic-369-compact-codec-boundary
  field
    samePointNineObserverCompressed : Bool
    samePointTwentySevenObserverCompressed : Bool
    bothFiniteObserversRoundTrip : Bool
    centrePreservedAsSemanticEscape : Bool
    nonCentreAntipodalPayloadUsesThreeBits : Bool
    thirdTritRetainedAsExplicitFrame : Bool
    analyticJRecoveredFromFiniteObserverCode : Bool
    continuousPhaseRecoveredFromFiniteObserverCode : Bool
    sourceExactRGBRecoveredFromFiniteObserverCode : Bool

canonicalFormulaic369CompactCodecBoundary : Formulaic369CompactCodecBoundary
canonicalFormulaic369CompactCodecBoundary =
  formulaic-369-compact-codec-boundary
    true true true true true true false false false
