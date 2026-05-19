module DASHI.Physics.Closure.CanonicalScheduleIndependentNaturalChargeWideningObstruction where

open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.CanonicalClosureCoarseObservable as CCO
open import DASHI.Physics.Closure.CanonicalScheduleIndependentNaturalChargeLaw as CSINCL

------------------------------------------------------------------------
-- Honest follow-on to the schedule-independent coarse law:
-- the nearest direct widenings are still obstructed on the current canonical
-- quotient, so the next landed theorem is a named no-go surface rather than a
-- forced stronger conserved quantity.
--
-- Blocked direct widenings:
-- * Gauge × basin × motif × eigenShadow
-- * Gauge × basin × mdl × motif × eigenShadow
--
-- This file stays intentionally narrow. It does not claim that no richer key
-- can ever control these channels; it only records that the immediate direct
-- conserved-charge widenings are not honestly available on the current
-- schedule-independent quotient.

record CanonicalScheduleIndependentNaturalChargeWideningObstruction : Setω where
  field
    baseLaw :
      CSINCL.CanonicalScheduleIndependentNaturalChargeLaw

    noProjectedNoMdlWidening :
      CCO.WidenedProjectedBridgeNoMdl → ⊥

    noFullConservedChargeWidening :
      CCO.WidenedConservedChargeScheduleBridge → ⊥

canonicalScheduleIndependentNaturalChargeWideningObstruction :
  CanonicalScheduleIndependentNaturalChargeWideningObstruction
canonicalScheduleIndependentNaturalChargeWideningObstruction =
  record
    { baseLaw = CSINCL.canonicalScheduleIndependentNaturalChargeLaw
    ; noProjectedNoMdlWidening = CCO.noWidenedProjectedBridgeNoMdl
    ; noFullConservedChargeWidening = CCO.noWidenedConservedChargeScheduleBridge
    }
